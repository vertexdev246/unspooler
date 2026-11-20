/**
 * PreEmptive JSDefender — self-defending loader layers.
 *
 * A protected chunk looks like
 *
 *   function (a, b) {
 *     const ARGS = Array.prototype.slice.call(arguments);
 *     return eval("(function N(P){const V=DEC(P,HASH(N.toString()));try{let X=eval(V);return X.apply(null,ARGS);}catch(E){… 'tampered' …}[function HASH…][function DEC…]})(\"<payload>\")");
 *   }
 *
 * HASH is a 32-bit checksum of the loader's own source text (so reformatting
 * breaks it) turned into a short key; DEC is decodeURI + XOR with that key.
 * The key's input — N.toString() — is exactly the loader's source text, which
 * we have, so each layer decrypts statically. Nothing is executed: both
 * algorithms are reimplemented here and their parameters are read off the
 * code (inline obfuscated form, or the plain `MIfnb.Db = function(source){…}`
 * helpers the first layer installs).
 *
 * Replacing the wrapper with the decrypted function is exact: it is called
 * with the wrapper's own arguments and `this` (apply(null, ARGS) in both), its
 * free names resolve to the same bindings (checked), and the tamper check can
 * only fire on modified code.
 */
import { createRequire } from "module";
const require = createRequire(import.meta.url);
const parser = require("@babel/parser");
const traverse = require("@babel/traverse").default;
const generate = require("@babel/generator").default;
const t = require("@babel/types");

const parse = (code) => parser.parse(code, { sourceType: "script", allowReturnOutsideFunction: true, errorRecovery: false });

const LOADER_RE = /^\(function ([A-Za-z_$][\w$]*)\(([A-Za-z_$][\w$]*)\)\{const ([A-Za-z_$][\w$]*)=/;

export function isJsdefender(code) {
  return /eval\("\(function [A-Za-z_$][\w$]*\([A-Za-z_$][\w$]*\)\{const [A-Za-z_$][\w$]*=[\w$.]+\([A-Za-z_$][\w$]*,[\w$.]+\([A-Za-z_$][\w$]*\.toString\(\)\)\);/.test(code)
    || /JSDEFENDER code has been tampered/.test(code);
}

/* ---------------- tiny exact constant folder for literal arithmetic ---------------- */
function num(n) {
  if (t.isNumericLiteral(n)) return n.value;
  if (t.isUnaryExpression(n, { operator: "-" })) { const v = num(n.argument); return v === null ? null : -v; }
  if (t.isBinaryExpression(n)) {
    const a = num(n.left), b = num(n.right);
    if (a === null || b === null) return null;
    switch (n.operator) {
      case "+": return a + b; case "-": return a - b; case "*": return a * b; case "/": return a / b; case "%": return a % b;
      case "&": return a & b; case "|": return a | b; case "^": return a ^ b; case "<<": return a << b; case ">>": return a >> b; case ">>>": return a >>> b;
    }
  }
  return null;
}

/**
 * Read the hash parameters from a HASH function node (inline, control-flow
 * flattened, or plain). Matches the distinctive expressions, independent of
 * statement order / state machines.
 */
export function hashParams(fn) {
  const p = {};
  const asStmt = (f) => (t.isFunctionDeclaration(f) ? t.cloneNode(f, true) : t.expressionStatement(t.cloneNode(f, true)));
  const wrap = t.file(t.program([asStmt(fn)]));
  const stateVars = new Set();
  traverse(wrap, {
    noScope: true,
    SwitchStatement(q) { if (t.isIdentifier(q.node.discriminant)) stateVars.add(q.node.discriminant.name); },
  });
  let checksumVar = null;
  traverse(wrap, {
    noScope: true,
    AssignmentExpression(q) {
      const n = q.node;
      // H ^= (S.charCodeAt(I) * MUL + S.charCodeAt(I >>> SH)) ^ XOR
      if (n.operator === "^=" && t.isIdentifier(n.left) && t.isBinaryExpression(n.right, { operator: "^" })) {
        const sum = n.right.left;
        if (t.isBinaryExpression(sum, { operator: "+" }) && t.isBinaryExpression(sum.left, { operator: "*" })) {
          const mul = num(sum.left.right), xor = num(n.right.right);
          const c2 = sum.right;
          const sh = t.isCallExpression(c2) && c2.arguments.length === 1 && t.isBinaryExpression(c2.arguments[0], { operator: ">>>" }) ? num(c2.arguments[0].right) : null;
          if (mul !== null && xor !== null && sh !== null) { checksumVar = n.left.name; Object.assign(p, { mul, xor, sh }); }
        }
      }
      // H = Math.floor(H / DIV)
      if (n.operator === "=" && t.isCallExpression(n.right) && t.isMemberExpression(n.right.callee) && t.isIdentifier(n.right.callee.property, { name: "floor" })
        && t.isBinaryExpression(n.right.arguments[0], { operator: "/" })) p.div = num(n.right.arguments[0].right);
    },
    BinaryExpression(q) {
      const n = q.node;
      if (n.operator === "%" && t.isIdentifier(n.left) && num(n.right) !== null && !stateVars.has(n.left.name)) p.mod = num(n.right);
    },
    ConditionalExpression(q) {
      // R >= THR ? String.fromCharCode(HB + (R - HS)) : String.fromCharCode(LB + R)
      const n = q.node;
      if (!t.isBinaryExpression(n.test, { operator: ">=" }) || num(n.test.right) === null) return;
      const ok = (c) => t.isCallExpression(c) && t.isMemberExpression(c.callee) && t.isIdentifier(c.callee.property, { name: "fromCharCode" }) && t.isBinaryExpression(c.arguments[0], { operator: "+" });
      if (!ok(n.consequent) || !ok(n.alternate)) return;
      const hb = n.consequent.arguments[0], lb = n.alternate.arguments[0];
      if (!t.isBinaryExpression(hb.right, { operator: "-" })) return;
      Object.assign(p, { thr: num(n.test.right), hiBase: num(hb.left), hiSub: num(hb.right.right), loBase: num(lb.left) });
    },
  });
  // seed: the initialiser of the checksum variable
  traverse(wrap, {
    noScope: true,
    VariableDeclarator(q) { if (t.isIdentifier(q.node.id, { name: checksumVar }) && num(q.node.init) !== null) p.seed = num(q.node.init); },
  });
  // key length: the one `i < CONST` that isn't a state-machine comparison
  const lens = new Set();
  traverse(wrap, {
    noScope: true,
    BinaryExpression(q) {
      const n = q.node;
      if (n.operator === "<" && t.isIdentifier(n.left) && !stateVars.has(n.left.name) && num(n.right) !== null) lens.add(num(n.right));
    },
  });
  if (lens.size === 1) p.len = [...lens][0];
  const need = ["seed", "mul", "xor", "sh", "div", "mod", "thr", "hiBase", "hiSub", "loBase", "len"];
  return need.every((k) => typeof p[k] === "number" && Number.isFinite(p[k])) ? p : null;
}

export function jsdHash(p, src) {
  let h = p.seed;
  for (let i = 0; i < src.length; i++) h ^= (src.charCodeAt(i) * p.mul + src.charCodeAt(i >>> p.sh)) ^ p.xor;
  let key = "";
  for (let i = 0; i < p.len; i++) {
    const r = h % p.mod;
    h = Math.floor(h / p.div);
    key += r >= p.thr ? String.fromCharCode(p.hiBase + (r - p.hiSub)) : String.fromCharCode(p.loBase + r);
  }
  return key;
}

/** decodeURI + XOR with the key, cycling */
export function jsdDecrypt(source, key) {
  source = decodeURI(source);
  let k = 0, out = "";
  for (let i = 0; i < source.length; i++) {
    out += String.fromCharCode(source.charCodeAt(i) ^ key.charCodeAt(k));
    if (++k >= key.length) k = 0;
  }
  return out;
}

/** a DEC function: decodeURI(param) then XOR with the key, cycling */
function isDecryptFn(fn) {
  const src = generate(fn).code;
  return /decodeURI\(/.test(src) && /fromCharCode\(/.test(src) && /\^/.test(src) && fn.params.length === 2;
}

/**
 * Helper functions the runtime installs as `X.Name = (function (source) {…})`.
 * Map "X.Name" -> FunctionExpression node.
 */
function collectMemberHelpers(ast) {
  const out = new Map();
  traverse(ast, {
    AssignmentExpression(q) {
      const n = q.node;
      if (n.operator !== "=" || !t.isMemberExpression(n.left) || n.left.computed || !t.isIdentifier(n.left.object) || !t.isIdentifier(n.left.property)) return;
      if (!t.isFunctionExpression(n.right)) return;
      const k = `${n.left.object.name}.${n.left.property.name}`;
      out.set(k, out.has(k) ? null : n.right); // assigned twice: ambiguous
    },
  });
  return out;
}

const calleeKey = (c) => (t.isIdentifier(c) ? c.name : t.isMemberExpression(c) && !c.computed && t.isIdentifier(c.object) && t.isIdentifier(c.property) ? `${c.object.name}.${c.property.name}` : null);

/** free identifiers of a function node (names not bound inside it) */
function freeNames(fnNode) {
  const names = new Set();
  const wrap = t.file(t.program([t.expressionStatement(t.cloneNode(fnNode, true))]));
  traverse(wrap, {
    Identifier(q) {
      if (!q.isReferencedIdentifier()) return;
      if (!q.scope.getBinding(q.node.name)) names.add(q.node.name);
    },
  });
  return names;
}

/**
 * Peel every loader layer, repeatedly (decrypted layers may contain more).
 * @returns {code, layers, errors}
 */
export function peelJsdefender(code, maxRounds = 64) {
  let layers = 0;
  let errors = [];
  for (let round = 0; round < maxRounds; round++) {
    errors = []; // a helper may only appear once an earlier layer is decrypted: report the last round
    const ast = parse(code);
    const helpers = collectMemberHelpers(ast);
    let changed = 0;
    traverse(ast, {
      FunctionExpression(fp) {
        const f = fp.node;
        const body = f.body.body;
        if (body.length !== 2) return;
        // const ARGS = Array.prototype.slice.call(arguments);
        const [d, r] = body;
        if (!t.isVariableDeclaration(d) || d.declarations.length !== 1 || !t.isIdentifier(d.declarations[0].id)) return;
        const argsName = d.declarations[0].id.name;
        const init = d.declarations[0].init;
        if (!(t.isCallExpression(init) && /^Array\.prototype\.slice\.call$/.test(generate(init.callee).code) && init.arguments.length === 1 && t.isIdentifier(init.arguments[0], { name: "arguments" }))) return;
        // return eval("<loader>")
        if (!t.isReturnStatement(r) || !t.isCallExpression(r.argument) || !t.isIdentifier(r.argument.callee, { name: "eval" }) || r.argument.arguments.length !== 1 || !t.isStringLiteral(r.argument.arguments[0])) return;
        const text = r.argument.arguments[0].value;
        const m = LOADER_RE.exec(text);
        if (!m) return;
        const [, nm, pn, vn] = m;
        let lAst;
        try { lAst = parse(text); } catch { return void errors.push("JSDefender: a loader layer does not parse"); }
        const call = lAst.program.body[0]?.expression;
        if (!t.isCallExpression(call) || !t.isFunctionExpression(call.callee) || call.arguments.length !== 1 || !t.isStringLiteral(call.arguments[0])) return;
        const loader = call.callee;
        const loaderSrc = text.slice(loader.start, loader.end); // == N.toString()
        // const V = DEC(P, HASH(N.toString()))
        const first = loader.body.body[0];
        const vd = t.isVariableDeclaration(first) && first.declarations[0];
        const decCall = vd && vd.init;
        if (!t.isCallExpression(decCall) || decCall.arguments.length !== 2 || !t.isCallExpression(decCall.arguments[1])) return;
        const hashCall = decCall.arguments[1];
        const decName = calleeKey(decCall.callee), hashName = calleeKey(hashCall.callee);
        // the loader must use the outer ARGS for apply(null, ARGS)
        if (!new RegExp(`\\.apply\\(null,${argsName.replace(/\$/g, "\\$")}\\)`).test(loaderSrc)) return;
        const local = new Map(loader.body.body.filter((s) => t.isFunctionDeclaration(s)).map((s) => [s.id.name, s]));
        const hashFn = local.get(hashName) || helpers.get(hashName);
        const decFn = local.get(decName) || helpers.get(decName);
        if (!hashFn || !decFn) return void errors.push(`JSDefender: loader helper ${!hashFn ? hashName : decName} not found`);
        if (!isDecryptFn(decFn)) return void errors.push("JSDefender: unrecognised loader decrypt function");
        const hp = hashParams(hashFn);
        if (!hp) return void errors.push("JSDefender: could not read the loader hash parameters");
        const inner = jsdDecrypt(call.arguments[0].value, jsdHash(hp, loaderSrc));
        let innerAst;
        try { innerAst = parse(inner); } catch { return void errors.push("JSDefender: a decrypted layer does not parse (wrong key?)"); }
        const innerFn = innerAst.program.body.length === 1 && innerAst.program.body[0].expression;
        if (!t.isFunctionExpression(innerFn)) return void errors.push("JSDefender: decrypted layer is not a function expression");
        // the inner function sees: its own scope, then the loader's, then the wrapper's
        const shadow = new Set([nm, pn, vn, argsName, ...loader.body.body.filter((s) => t.isFunctionDeclaration(s)).map((s) => s.id.name), ...f.params.map((q) => q.name)]);
        for (const name of freeNames(innerFn)) if (shadow.has(name)) return void errors.push(`JSDefender: decrypted layer reads loader-scope name ${name}`);
        if (innerFn.params.length !== f.params.length) return void errors.push("JSDefender: decrypted layer has a different parameter count");
        fp.replaceWith(innerFn);
        fp.skip();
        changed++;
      },
    });
    if (!changed) break;
    layers += changed;
    code = generate(ast, { comments: true }).code;
  }
  return { code, layers, errors };
}

/* ======================= helper / constant folding ======================= */
import { makeEvaluator, Unsupported, FunctionText } from "./pureeval.mjs";

const litNode = (v) => {
  if (typeof v === "string") return t.stringLiteral(v);
  if (typeof v === "boolean") return t.booleanLiteral(v);
  if (v === null) return t.nullLiteral();
  if (v === undefined) return t.unaryExpression("void", t.numericLiteral(0));
  if (typeof v === "number") {
    if (Number.isNaN(v)) return t.binaryExpression("/", t.numericLiteral(0), t.numericLiteral(0));
    if (v === Infinity) return t.binaryExpression("/", t.numericLiteral(1), t.numericLiteral(0));
    if (v === -Infinity) return t.unaryExpression("-", t.binaryExpression("/", t.numericLiteral(1), t.numericLiteral(0)));
    if (v < 0 || Object.is(v, -0)) return t.unaryExpression("-", t.numericLiteral(-v));
    return t.numericLiteral(v);
  }
  return null;
};
// the literal forms litNode emits (incl. 0/0, 1/0, -(1/0)) count as folded, or folding would loop
const isDivZero = (n) => t.isBinaryExpression(n, { operator: "/" }) && t.isNumericLiteral(n.left) && t.isNumericLiteral(n.right, { value: 0 });
const isConstNode = (n) => t.isStringLiteral(n) || t.isNumericLiteral(n) || t.isBooleanLiteral(n) || t.isNullLiteral(n) || isDivZero(n)
  || (t.isUnaryExpression(n, { operator: "-" }) && (t.isNumericLiteral(n.argument) || isDivZero(n.argument)))
  || (t.isUnaryExpression(n, { operator: "void" }) && t.isNumericLiteral(n.argument));
const constOf = (n) => {
  if (isDivZero(n)) return n.left.value / 0;
  if (t.isUnaryExpression(n, { operator: "-" })) return -constOf(n.argument);
  if (t.isUnaryExpression(n, { operator: "void" })) return undefined;
  if (t.isNullLiteral(n)) return null;
  return n.value;
};

/** subtree made only of literals / [] / unary / binary / member / ++ on fresh arrays: a pure coercion expression */
function isPureCoercion(n) {
  if (isConstNode(n) || t.isArrayExpression(n)) return n.elements ? n.elements.every((e) => e && !t.isSpreadElement(e) && isPureCoercion(e)) : true;
  if (t.isUnaryExpression(n)) return ["!", "+", "-", "~"].includes(n.operator) && isPureCoercion(n.argument);
  if (t.isBinaryExpression(n)) return n.operator !== "in" && n.operator !== "instanceof" && isPureCoercion(n.left) && isPureCoercion(n.right);
  if (t.isMemberExpression(n)) return n.computed && isPureCoercion(n.object) && isPureCoercion(n.property);
  if (t.isUpdateExpression(n)) return t.isMemberExpression(n.argument) && t.isArrayExpression(n.argument.object) && isPureCoercion(n.argument);
  return false;
}

/**
 * Fold calls to the runtime's constant helpers (zero-arg char/number helpers,
 * `RUNTIME.k = function(){return C}`, string decryptors called with constants)
 * and pure coercion expressions, to a fixpoint. Calls are only folded when
 * every argument is a literal and the evaluator stays inside its pure subset.
 */
export function foldJsdefenderHelpers(ast, { maxRounds = 30 } = {}) {
  let folded = 0;
  for (let round = 0; round < maxRounds; round++) {
    traverse.cache.clear?.();
    // scope info
    let programPath = null;
    traverse(ast, { Program(p) { programPath = p; p.scope.crawl(); p.stop(); } });
    // member helpers: OBJ.k = function(){…}, assigned once; computed writes must provably not alias
    const memberDefs = new Map(), memberCount = new Map();
    const computedWrites = [];
    traverse(ast, {
      AssignmentExpression(q) {
        const l = q.node.left;
        if (q.node.operator !== "=" || !t.isMemberExpression(l) || !t.isIdentifier(l.object)) return;
        if (l.computed && !t.isStringLiteral(l.property)) { computedWrites.push({ obj: l.object.name, key: l.property, path: q }); return; }
        const k = `${l.object.name}.${l.computed ? l.property.value : l.property.name}`;
        memberCount.set(k, (memberCount.get(k) || 0) + 1);
        const r = q.node.right;
        if (t.isFunctionExpression(r) || t.isArrowFunctionExpression(r)) memberDefs.set(k, { node: r, path: q.get("right") });
        else if (t.isIdentifier(r)) {
          // OBJ["k"] = someFunctionDeclaration
          const b = q.scope.getBinding(r.name);
          if (b && !b.constantViolations.length && b.path.isFunctionDeclaration()) memberDefs.set(k, { node: b.path.node, path: b.path });
        }
      },
    });
    const resolveFn = (name, path) => {
      const b = (path || programPath).scope.getBinding(name);
      if (!b || b.constantViolations.length || !b.path.isFunctionDeclaration()) return null;
      return { node: b.path.node, path: b.path };
    };
    const tables = findStringTables(ast, programPath, resolveFn);
    const resolveConst = (name, path) => {
      const b = (path || programPath).scope.getBinding(name);
      return b && tables.has(b) ? { v: tables.get(b) } : null;
    };
    const unsafeObjs = new Set(); // objects with a computed write we can't resolve
    const ev0 = makeEvaluator({ resolveFn, resolveMember: () => null, resolveConst });
    const computedKeys = new Set();
    for (const w of computedWrites) {
      if (!memberDefs.size) break;
      if (![...memberDefs.keys()].some((k) => k.startsWith(w.obj + "."))) continue;
      try { computedKeys.add(`${w.obj}.${String(ev0.expr(w.key, w.path))}`); } catch (e) { if (!(e instanceof Unsupported) && !(e instanceof RangeError)) throw e; unsafeObjs.add(w.obj); }
    }
    const resolveMember = (obj, prop) => {
      const k = `${obj}.${prop}`;
      if (unsafeObjs.has(obj) || memberCount.get(k) !== 1 || computedKeys.has(k)) return null;
      return memberDefs.get(k) || null;
    };
    const ev = makeEvaluator({ resolveFn, resolveMember, resolveConst });
    if (process.env.JSDDBG) console.error("tables", tables.size, "unsafe objects", unsafeObjs.size, "memberDefs", memberDefs.size);
    const traps = neutraliseConsoleTraps(ast, () => ev);
    if (traps) { folded += traps; continue; } // re-crawl with the rewritten traps
    const cache = new Map();
    let changed = 0;
    traverse(ast, {
      CallExpression: {
        exit(q) {
          const n = q.node;
          if (!n.arguments.every(isConstNode)) return;
          let fn = null;
          if (t.isIdentifier(n.callee)) fn = resolveFn(n.callee.name, q);
          else if (t.isMemberExpression(n.callee) && !n.callee.computed && t.isIdentifier(n.callee.object) && !q.scope.getBinding(n.callee.object.name)?.path.isFunction?.())
            fn = resolveMember(n.callee.object.name, n.callee.property.name);
          if (!fn) return;
          const args = n.arguments.map(constOf);
          const key = fn.node.start + ":" + JSON.stringify(args.map((a) => (a === undefined ? { u: 1 } : a)));
          let v;
          if (cache.has(key)) v = cache.get(key);
          else {
            const m0 = process.env.JSDDBG ? process.memoryUsage().heapUsed : 0;
            if (process.env.JSDDBG2) require("fs").appendFileSync(process.env.JSDDBG2, generate(n).code.slice(0, 160) + "\n");
            try { v = { ok: ev.call(fn, args) }; } catch (e) { if (!(e instanceof Unsupported) && !(e instanceof RangeError)) throw e; v = null; }
            cache.set(key, v);
            if (process.env.JSDDBG && process.memoryUsage().heapUsed - m0 > 2e8) console.error("BIG", generate(n).code.slice(0, 120), Math.round(process.memoryUsage().heapUsed / 1e6) + "MB");
          }
          if (!v || v.ok instanceof FunctionText) return;
          if (typeof v.ok === "string" && v.ok.length > 100000) return;
          const lit = litNode(v.ok);
          if (!lit) return;
          q.replaceWith(lit);
          changed++;
        },
      },
      "UnaryExpression|BinaryExpression|MemberExpression|UpdateExpression": {
        exit(q) {
          if (isConstNode(q.node)) return;
          if (!isPureCoercion(q.node)) return;
          // only the maximal pure subtree (an array parent never becomes a literal itself)
          if (isPureCoercion(q.parent) && !t.isStatement(q.parent) && !t.isArrayExpression(q.parent)) return;
          let v;
          if (process.env.JSDDBG2) require("fs").appendFileSync(process.env.JSDDBG2, "COERCE " + generate(q.node).code.slice(0, 160) + "\n");
          try { v = ev.expr(q.node, q); } catch (e) { if (!(e instanceof Unsupported) && !(e instanceof RangeError)) throw e; return; }
          const lit = litNode(v);
          if (!lit) return;
          q.replaceWith(lit);
          changed++;
        },
      },
    });
    folded += changed;
    if (process.env.JSDDBG) console.error("fold round", round, "changed", changed, "cache", cache.size, "mem", Math.round(process.memoryUsage().heapUsed / 1e6) + "MB");
    if (!changed) break;
  }
  return folded;
}


/**
 * The console-cloaking tamper trap:
 *   function W() { const q = G()["console"]; return q ? (q + [])[x % 10] : S(q + [], 19); }
 * JSDefender's runtime deletes global.console at startup, before anything
 * uses W(), and splices W() into method names ("fromCh" + W() + "arCode"):
 * any run in which the program works at all has W() === "" (otherwise every
 * decoded name breaks). Its body is rewritten to `return ""` with a comment;
 * the cloaking itself (real behaviour) is left alone.
 */
export function neutraliseConsoleTraps(ast, evaluatorFor) {
  let n = 0;
  traverse(ast, {
    FunctionDeclaration(q) {
      const b = q.node.body.body;
      if (q.node.params.length || b.length !== 2) return;
      const [d, r] = b;
      if (!t.isVariableDeclaration(d) || d.declarations.length !== 1 || !t.isIdentifier(d.declarations[0].id)) return;
      const qn = d.declarations[0].id.name;
      const init = d.declarations[0].init;
      if (!t.isMemberExpression(init, { computed: true }) || !t.isStringLiteral(init.property, { value: "console" }) || !t.isCallExpression(init.object)) return;
      if (!t.isReturnStatement(r) || !t.isConditionalExpression(r.argument) || !t.isIdentifier(r.argument.test, { name: qn })) return;
      const alt = r.argument.alternate;
      if (!t.isCallExpression(alt) || alt.arguments.length !== 2 || !t.isNumericLiteral(alt.arguments[1])) return;
      // the clean-environment branch must provably give ""
      let v;
      try { v = evaluatorFor(q).expr(t.callExpression(alt.callee, [t.stringLiteral("undefined"), alt.arguments[1]]), q); } catch { return; }
      if (v !== "") return;
      q.node.body.body = [t.returnStatement(t.stringLiteral(""))];
      t.addComment(q.node, "leading", " JSDefender tamper trap: returns \"\" once its console cloaking has run (always, in a working run) ", false);
      n++;
    },
  });
  return n;
}

/**
 * The string table decoder:
 *   function U() { T = []; …for each A[i]: s = ""; for each char c: s += F["fromCharCode"](A[i]["charCodeAt"](j) ^ K); T["push"](s) }
 * with T an outer `let` written nowhere else and A an outer array of string
 * literals written nowhere. Returns Map(binding of T -> decoded array).
 */
function findStringTables(ast, programPath, resolveFn) {
  const out = new Map();
  traverse(ast, {
    FunctionDeclaration(q) {
      const body = q.node.body.body;
      const first = body[0];
      if (!t.isExpressionStatement(first) || !t.isAssignmentExpression(first.expression, { operator: "=" }) || !t.isIdentifier(first.expression.left)
        || !t.isArrayExpression(first.expression.right) || first.expression.right.elements.length) return;
      const tName = first.expression.left.name;
      const tb = q.scope.getBinding(tName);
      if (!tb || tb.path.scope === q.scope || tb.constantViolations.length !== 1 || tb.constantViolations[0].node !== first.expression) return;
      // computed member names must provably be these strings (literal, or a const bound to one)
      const nameOf = (n, scope) => {
        if (t.isStringLiteral(n)) return n.value;
        if (!t.isIdentifier(n)) return null;
        const b = scope.getBinding(n.name);
        return b && b.kind === "const" && b.path.isVariableDeclarator() && t.isStringLiteral(b.path.node.init) ? b.path.node.init.value : null;
      };
      // K: the XOR key in  F["fromCharCode"](A[i]["charCodeAt"](j) ^ K)
      let key = null, arrName = null, pushOk = false;
      q.traverse({
        BinaryExpression(b) {
          if (b.node.operator !== "^" || !t.isNumericLiteral(b.node.right)) return;
          const c = b.node.left;
          if (!t.isCallExpression(c) || !t.isMemberExpression(c.callee, { computed: true })) return;
          const outer = b.parentPath;
          if (nameOf(c.callee.property, b.scope) === "charCodeAt" && outer.isCallExpression() && t.isMemberExpression(outer.node.callee, { computed: true })
            && nameOf(outer.node.callee.property, b.scope) === "fromCharCode") key = b.node.right.value;
        },
        MemberExpression(m) {
          // A[i] where A is an outer array of string literals
          if (!m.node.computed || !t.isIdentifier(m.node.object)) return;
          const ab = m.scope.getBinding(m.node.object.name);
          if (!ab || ab.constantViolations.length || !ab.path.isVariableDeclarator() || !t.isArrayExpression(ab.path.node.init)) return;
          if (!ab.path.node.init.elements.every((e) => t.isStringLiteral(e))) return;
          // A must only ever be read through A[...]
          if (!ab.referencePaths.every((r) => r.parentPath.isMemberExpression() && r.key === "object" && !(r.parentPath.parentPath.isAssignmentExpression() && r.parentPath.key === "left") && !r.parentPath.parentPath.isUpdateExpression())) return;
          arrName = ab;
        },
        CallExpression(c) {
          if (t.isMemberExpression(c.node.callee, { computed: true }) && t.isIdentifier(c.node.callee.object, { name: tName }) && c.node.arguments.length === 1
            && nameOf(c.node.callee.property, c.scope) === "push") pushOk = true;
        },
      });
      if (key === null || !arrName || !pushOk) return;
      // T must otherwise only be read as T[i]
      if (!tb.referencePaths.every((r) => r.parentPath.isMemberExpression() && r.key === "object" && !(r.parentPath.parentPath.isAssignmentExpression() && r.parentPath.key === "left"))) return;
      const strs = arrName.path.node.init.elements.map((e) => e.value);
      out.set(tb, strs.map((s) => { let o = ""; for (let i = 0; i < s.length; i++) o += String.fromCharCode(s.charCodeAt(i) ^ key); return o; }));
    },
  });
  return out;
}

/**
 * Conservative dead-declaration elimination for the recovered program: removes
 * function declarations and pure variable declarators that have no remaining
 * references (the folding + CFF passes leave the runtime's string/number helper
 * functions dead). Only removes things whose definition has no side effects, so
 * it never changes behaviour; iterates to a fixpoint. Member assignments on the
 * runtime object are left alone (that object may be enumerated).
 */
export function eliminateDeadDeclarations(ast) {
  const pureInit = (n) => {
    if (n == null) return true;
    if (t.isLiteral(n) && !t.isTemplateLiteral(n)) return true;
    if (t.isFunctionExpression(n) || t.isArrowFunctionExpression(n) || t.isClassExpression(n)) return true;
    if (t.isIdentifier(n) || t.isThisExpression(n)) return true;
    if (t.isUnaryExpression(n)) return n.operator !== "delete" && pureInit(n.argument);
    if (t.isBinaryExpression(n)) return pureInit(n.left) && pureInit(n.right);
    if (t.isLogicalExpression(n)) return pureInit(n.left) && pureInit(n.right);
    if (t.isMemberExpression(n)) return pureInit(n.object) && (!n.computed || pureInit(n.property));
    if (t.isArrayExpression(n)) return n.elements.every((e) => e == null || (!t.isSpreadElement(e) && pureInit(e)));
    if (t.isObjectExpression(n)) return n.properties.every((p) => t.isObjectProperty(p) && !p.computed && pureInit(p.value));
    return false;
  };
  const exported = (p) => { for (let q = p; q; q = q.parentPath) if (q.isExportNamedDeclaration() || q.isExportDefaultDeclaration()) return true; return false; };

  let removed = 0;
  for (let round = 0; round < 40; round++) {
    traverse(ast, { Program(p) { p.scope.crawl(); p.stop(); } });
    const kill = [];
    traverse(ast, {
      FunctionDeclaration(p) {
        if (!p.node.id) return;
        const b = p.scope.getBinding(p.node.id.name);
        if (b && b.referencePaths.length === 0 && b.constantViolations.length === 0 && !exported(p)) kill.push(p);
      },
      VariableDeclarator(p) {
        if (!t.isIdentifier(p.node.id)) return;
        // never touch a declarator that is part of a for/for-in/for-of head
        const decl = p.parentPath;
        if (!decl.isVariableDeclaration() || !decl.parentPath.isBlockStatement() && !decl.parentPath.isProgram()) return;
        const b = p.scope.getBinding(p.node.id.name);
        if (!b || b.referencePaths.length !== 0 || b.constantViolations.length !== 0) return;
        if (!pureInit(p.node.init) || exported(decl)) return;
        kill.push(p);
      },
    });
    if (!kill.length) break;
    for (const p of kill) {
      try {
        if (p.removed || !p.node) continue;
        if (p.isVariableDeclarator()) {
          const d = p.parentPath;
          if (!d || d.removed || !d.node) continue;
          if (d.node.declarations.length === 1) d.remove(); else p.remove();
        } else p.remove();
        removed++;
      } catch { /* path became stale from an ancestor removal this round */ }
    }
  }
  return removed;
}
