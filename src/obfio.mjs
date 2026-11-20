/**
 * javascript-obfuscator (obfuscator.io) reversal passes.
 *
 * Templates: src/custom-code-helpers/string-array/templates/* (v5.x):
 *   function A() { const arr = [ ...strings ]; A = function () { return arr; }; return A(); }
 *   (function (f, target) { const arr = f(); while (true) { try {
 *       const e = <parseInt(W(i)) / n ... arithmetic>;
 *       if (e === target) break; else arr.push(arr.shift());
 *     } catch (e) { arr.push(arr.shift()); } } })(A, target);
 *   function W(index, key) { index = index - SHIFT; const arr = A(); let value = arr[index];
 *       [base64 | rc4 decode, cached per index]; return value; }
 * plus wrappers: `var w = W;` aliases and `function w(a, b, c) { return W(b - 0x1a, c); }`.
 *
 * Nothing in the input is executed: rotation is found by evaluating the
 * comparison expression with a native mirror of the decoders.
 */
import * as t from "@babel/types";
const require = (await import("module")).createRequire(import.meta.url);
const traverse = require("@babel/traverse").default;

/* ---------------------------------------------------------- decoders */
// mirror of AtobTemplate (alphabet taken from the decoder itself)
function atobMirror(input, chars) {
  let output = "";
  let temp = "";
  for (let bc = 0, bs, buffer, idx = 0; (buffer = input.charAt(idx++)); ~buffer && ((bs = bc % 4 ? bs * 64 + buffer : buffer), bc++ % 4) ? (output += String.fromCharCode(255 & (bs >> ((-2 * bc) & 6)))) : 0) {
    buffer = chars.indexOf(buffer);
  }
  for (let k = 0, length = output.length; k < length; k++) temp += "%" + ("00" + output.charCodeAt(k).toString(16)).slice(-2);
  return decodeURIComponent(temp);
}
// mirror of Rc4Template
function rc4Mirror(str, key, chars) {
  const s = [];
  let j = 0;
  let x;
  let output = "";
  str = atobMirror(str, chars);
  let i;
  for (i = 0; i < 256; i++) s[i] = i;
  for (i = 0; i < 256; i++) {
    j = (j + s[i] + key.charCodeAt(i % key.length)) % 256;
    x = s[i];
    s[i] = s[j];
    s[j] = x;
  }
  i = 0;
  j = 0;
  for (let y = 0; y < str.length; y++) {
    i = (i + 1) % 256;
    j = (j + s[i]) % 256;
    x = s[i];
    s[i] = s[j];
    s[j] = x;
    output += String.fromCharCode(str.charCodeAt(y) ^ s[(s[i] + s[j]) % 256]);
  }
  return output;
}

/* --------------------------------------------------- small helpers */
const memberKey = (m) =>
  m.computed ? (t.isStringLiteral(m.property) ? m.property.value : null) : t.isIdentifier(m.property) ? m.property.name : null;
function nodeText(node) {
  return JSON.stringify(node, (k, v) => (["loc", "start", "end", "extra", "leadingComments", "trailingComments"].includes(k) ? undefined : v));
}
function crawl(ast) {
  let pp = null;
  traverse(ast, {
    Program(p) {
      p.scope.crawl();
      pp = p;
      p.stop();
    },
  });
  return pp;
}
/** evaluate a constant expression; `env` maps identifier names to values */
function evalConst(n, env = new Map(), lookup = null) {
  if (lookup && t.isMemberExpression(n)) return lookup(n);
  if (t.isNumericLiteral(n) || t.isStringLiteral(n) || t.isBooleanLiteral(n)) return { v: n.value };
  if (t.isNullLiteral(n)) return { v: null };
  if (t.isIdentifier(n)) return env.has(n.name) ? { v: env.get(n.name) } : n.name === "undefined" ? { v: undefined } : null;
  if (t.isParenthesizedExpression(n)) return evalConst(n.expression, env, lookup);
  if (t.isUnaryExpression(n)) {
    // ![] / !![] (simplify / boolean literal transformer)
    if (n.operator === "!" && t.isArrayExpression(n.argument) && n.argument.elements.length === 0) return { v: false };
    const a = evalConst(n.argument, env, lookup);
    if (!a) return null;
    switch (n.operator) {
      case "-": return { v: -a.v };
      case "+": return { v: +a.v };
      case "!": return { v: !a.v };
      case "~": return { v: ~a.v };
      case "void": return { v: undefined };
      case "typeof": return { v: typeof a.v };
    }
    return null;
  }
  if (t.isBinaryExpression(n)) {
    const a = evalConst(n.left, env, lookup);
    if (!a) return null;
    const b = evalConst(n.right, env, lookup);
    if (!b) return null;
    const x = a.v, y = b.v;
    switch (n.operator) {
      case "+": return { v: x + y };
      case "-": return { v: x - y };
      case "*": return { v: x * y };
      case "/": return { v: x / y };
      case "%": return { v: x % y };
      case "**": return { v: x ** y };
      case "|": return { v: x | y };
      case "&": return { v: x & y };
      case "^": return { v: x ^ y };
      case "<<": return { v: x << y };
      case ">>": return { v: x >> y };
      case ">>>": return { v: x >>> y };
      case "==": return { v: x == y }; // eslint-disable-line eqeqeq
      case "!=": return { v: x != y }; // eslint-disable-line eqeqeq
      case "===": return { v: x === y };
      case "!==": return { v: x !== y };
      case "<": return { v: x < y };
      case ">": return { v: x > y };
      case "<=": return { v: x <= y };
      case ">=": return { v: x >= y };
    }
    return null;
  }
  return null;
}

/**
 * stringArrayCallsTransform moves call arguments into local constant objects:
 *   var Z = { L: 0x15 }, q = A;  ...  q(Z.L)
 * Returns a lookup for evalConst that reads `Z.L` when Z is bound to an object
 * literal that is never written and only ever read through plain member reads.
 */
function constObjectLookup(scope) {
  const cache = new Map();
  const propsOf = (b) => {
    if (cache.has(b)) return cache.get(b);
    let props = null;
    const init = b.path.isVariableDeclarator() ? b.path.node.init : null;
    if (b.constantViolations.length === 0 && t.isObjectExpression(init)) {
      props = new Map();
      for (const pp of init.properties) {
        const k = t.isObjectProperty(pp) && !pp.computed ? (t.isIdentifier(pp.key) ? pp.key.name : t.isStringLiteral(pp.key) ? pp.key.value : null) : null;
        if (k === null || props.has(k)) { props = null; break; }
        props.set(k, pp.value);
      }
      if (props)
        for (const r of b.referencePaths) {
          const mp = r.parentPath;
          const ok = mp.isMemberExpression() && r.key === "object" && objMemberKey(mp.node) !== null &&
            !(mp.parentPath.isAssignmentExpression() && mp.key === "left") && !mp.parentPath.isUpdateExpression() &&
            !mp.parentPath.isUnaryExpression({ operator: "delete" }) && !(mp.parentPath.isCallExpression() && mp.key === "callee");
          if (!ok) { props = null; break; }
        }
    }
    cache.set(b, props);
    return props;
  };
  const lookup = (n, sc = scope) => {
    if (!t.isIdentifier(n.object)) return null;
    const k = objMemberKey(n);
    if (k === null) return null;
    const b = sc.getBinding(n.object.name);
    if (!b) return null;
    const props = propsOf(b);
    if (!props || !props.has(k)) return null;
    return evalConst(props.get(k), new Map(), null);
  };
  return lookup;
}
function objMemberKey(m) {
  if (!m.computed && t.isIdentifier(m.property)) return m.property.name;
  if (m.computed && t.isStringLiteral(m.property)) return m.property.value;
  return null;
}

/* ================================================ string array pass */
/**
 * Returns the number of string-array calls replaced, or 0.
 * Errors (with reasons) are pushed to ctx.errors; nothing is changed then.
 */
export function reverseStringArray(ast, ctx) {
  let total = 0;
  for (let round = 0; round < 8; round++) {
    const n = reverseOneArray(ast, ctx);
    if (!n) break;
    total += n;
  }
  if (total) ctx.stats.obfioStringArray = { replaced: total };
}

function reverseOneArray(ast, ctx) {
  const programPath = crawl(ast);

  /* 1. array functions: function A() { var arr = [...]; A = function () { return arr; }; return A(); } */
  const arrays = new Map(); // binding -> { path, values }
  traverse(ast, {
    FunctionDeclaration(path) {
      const fn = path.node;
      if (fn.params.length || !fn.id || path.node.__obfioSkip) return;
      const body = fn.body.body;
      if (body.length !== 3) return;
      const [decl, reassign, ret] = body;
      if (!t.isVariableDeclaration(decl) || decl.declarations.length !== 1 || !t.isIdentifier(decl.declarations[0].id)) return;
      const arr = decl.declarations[0].init;
      if (!t.isArrayExpression(arr) || !arr.elements.every((e) => t.isStringLiteral(e))) return;
      const arrName = decl.declarations[0].id.name;
      if (
        !t.isExpressionStatement(reassign) ||
        !t.isAssignmentExpression(reassign.expression, { operator: "=" }) ||
        !t.isIdentifier(reassign.expression.left, { name: fn.id.name }) ||
        !t.isFunctionExpression(reassign.expression.right) ||
        reassign.expression.right.body.body.length !== 1 ||
        !t.isReturnStatement(reassign.expression.right.body.body[0]) ||
        !t.isIdentifier(reassign.expression.right.body.body[0].argument, { name: arrName })
      )
        return;
      if (!t.isReturnStatement(ret) || !t.isCallExpression(ret.argument) || !t.isIdentifier(ret.argument.callee, { name: fn.id.name }) || ret.argument.arguments.length)
        return;
      const b = path.parentPath.scope.getBinding(fn.id.name);
      if (b && b.path.node === fn) arrays.set(b, { path, values: arr.elements.map((e) => e.value) });
    },
  });
  if (!arrays.size) return 0;

  /* 2. decoder functions W(index, key) over an array function */
  const decoders = new Map(); // binding -> info
  traverse(ast, {
    FunctionDeclaration(path) {
      const fn = path.node;
      if (!fn.id || fn.params.length < 1 || fn.params.length > 2 || !fn.params.every((p) => t.isIdentifier(p))) return;
      const idx = fn.params[0].name;
      const body = fn.body.body;
      // first statement: index = index - SHIFT
      const first = body[0];
      if (
        !t.isExpressionStatement(first) ||
        !t.isAssignmentExpression(first.expression, { operator: "=" }) ||
        !t.isIdentifier(first.expression.left, { name: idx }) ||
        !t.isBinaryExpression(first.expression.right, { operator: "-" }) ||
        !t.isIdentifier(first.expression.right.left, { name: idx })
      )
        return;
      const shift = evalConst(first.expression.right.right);
      if (!shift || typeof shift.v !== "number") return;
      // the array function it reads
      let arrBinding = null;
      path.traverse({
        CallExpression(cp) {
          if (arrBinding || !t.isIdentifier(cp.node.callee) || cp.node.arguments.length) return;
          const b = cp.scope.getBinding(cp.node.callee.name);
          if (b && arrays.has(b)) arrBinding = b;
        },
      });
      if (!arrBinding) return;
      const text = nodeText(fn.body);
      let kind = "none";
      let chars = null;
      if (text.includes("decodeURIComponent")) {
        // RC4 is the only variant that uses the key parameter (numbers inside
        // the decoder may be rewritten as arithmetic, so don't rely on 256)
        const keyName = fn.params[1]?.name;
        const keyBinding = keyName ? path.scope.getOwnBinding(keyName) : null;
        kind = keyBinding && keyBinding.referencePaths.length ? "rc4" : "base64";
        path.traverse({
          StringLiteral(sp) {
            if (sp.node.value.length === 65 && /^[a-zA-Z0-9+/=]+$/.test(sp.node.value)) chars = sp.node.value;
          },
        });
        if (!chars) return;
      }
      const b = path.parentPath.scope.getBinding(fn.id.name);
      if (b && b.path.node === fn) decoders.set(b, { path, shift: shift.v, kind, chars, arrBinding, keyParam: fn.params[1]?.name });
    },
  });
  if (!decoders.size) return 0;

  /* 3. resolution of callees: decoder, alias (`var w = W`), wrapper function */
  const decode = (info, rotated, index, key) => {
    const raw = rotated[index - info.shift];
    if (raw === undefined) return undefined;
    if (info.kind === "none") return raw;
    if (info.kind === "base64") return atobMirror(raw, info.chars);
    return rc4Mirror(raw, String(key), info.chars);
  };
  // binding -> function that maps arg values to { decoder, index, key }
  const resolverCache = new Map();
  function resolverOf(b, depth = 0) {
    if (!b || depth > 20) return null;
    if (resolverCache.has(b)) return resolverCache.get(b);
    resolverCache.set(b, null); // cycle guard
    let r = null;
    if (decoders.has(b)) {
      const info = decoders.get(b);
      r = (args) => ({ info, index: args[0], key: args[1] });
    } else if (b.path.isVariableDeclarator() && t.isIdentifier(b.path.node.init) && b.constantViolations.length === 0) {
      // alias: var w = W
      const target = resolverOf(b.path.scope.getBinding(b.path.node.init.name), depth + 1);
      if (target) r = target;
    } else if ((b.path.isFunctionDeclaration() || b.path.isVariableDeclarator()) && b.constantViolations.length === 0) {
      // wrapper: function w(a, b, c) { return W(<expr of params>, <expr of params>); }
      const fnPath = b.path.isFunctionDeclaration() ? b.path : b.path.get("init");
      const fn = fnPath.node;
      // leading `var o = { k: <const> }` statements are inert (stringArrayCallsTransform)
      const stmts = t.isFunction(fn) && t.isBlockStatement(fn.body) ? fn.body.body : [];
      const inertObjDecl = (st) =>
        t.isVariableDeclaration(st) &&
        st.declarations.every((d) => t.isIdentifier(d.id) && t.isObjectExpression(d.init) &&
          d.init.properties.every((pp) => t.isObjectProperty(pp) && !pp.computed && evalConst(pp.value)));
      if (t.isFunction(fn) && fn.params.every((p) => t.isIdentifier(p)) && stmts.length >= 1 && t.isReturnStatement(stmts[stmts.length - 1]) && stmts.slice(0, -1).every(inertObjDecl)) {
        const call = stmts[stmts.length - 1].argument;
        const lk = constObjectLookup(fnPath.get("body").scope);
        if (t.isCallExpression(call) && t.isIdentifier(call.callee)) {
          const inner = resolverOf(fnPath.scope.getBinding(call.callee.name), depth + 1);
          if (inner) {
            const params = fn.params.map((p) => p.name);
            r = (args) => {
              const env = new Map(params.map((p, i) => [p, args[i]]));
              const vals = [];
              for (const a of call.arguments) {
                const v = evalConst(a, env, lk);
                if (!v) return null;
                vals.push(v.v);
              }
              return inner(vals);
            };
          }
        }
      }
    }
    resolverCache.set(b, r);
    return r;
  }

  /* 4. rotation per array function */
  const rotation = new Map(); // array binding -> rotated values
  const rotateIIFEs = new Map(); // array binding -> statement path
  const unproven = new Set(); // arrays with a rotation loop whose rotation we could not prove
  traverse(ast, {
    CallExpression(cp) {
      const c = cp.node;
      if (!t.isFunctionExpression(c.callee) || c.arguments.length !== 2 || !t.isIdentifier(c.arguments[0])) return;
      const ab = cp.scope.getBinding(c.arguments[0].name);
      if (!ab || !arrays.has(ab)) return;
      unproven.add(ab); // until a rotation is proven below
      const target = evalConst(c.arguments[1]);
      if (!target) return;
      // the comparison expression: the init of the declaration whose value is compared
      let expr = null;
      cp.get("callee").traverse({
        IfStatement(ip) {
          const test = ip.node.test;
          if (t.isBinaryExpression(test, { operator: "===" }) && t.isIdentifier(test.left) && t.isIdentifier(test.right, { name: c.callee.params[1]?.name })) {
            const vb = ip.scope.getBinding(test.left.name);
            if (vb && vb.path.isVariableDeclarator()) expr = vb.path.get("init");
          }
        },
      });
      if (!expr) return;
      const values = arrays.get(ab).values;
      const rotLookup = constObjectLookup(expr.scope);
      // evaluate for each rotation; calls inside resolve through the same machinery
      const evalWith = (rot) => {
        const ev = (n) => {
          if (t.isCallExpression(n) && t.isIdentifier(n.callee, { name: "parseInt" }) && n.arguments.length === 1) {
            const s = ev(n.arguments[0]);
            return parseInt(s);
          }
          if (t.isCallExpression(n) && t.isIdentifier(n.callee)) {
            const nb = expr.scope.getBinding(n.callee.name);
            const res = resolverOf(nb);
            if (!res) throw new Error("unresolvable call in rotation");
            const args = n.arguments.map((a) => {
              const v = evalConst(a, new Map(), rotLookup);
              if (!v) throw new Error("non-constant arg in rotation");
              return v.v;
            });
            const target2 = res(args);
            if (!target2) throw new Error("unresolvable call in rotation");
            if (target2.info.arrBinding !== ab) throw new Error("rotation reads another array");
            const v = decode(target2.info, rot, Number(target2.index), target2.key);
            if (process.env.OBFIODBG2) console.error("DEC", target2.info.kind, target2.index, JSON.stringify(target2.key), JSON.stringify(v));
            return v;
          }
          if (t.isUnaryExpression(n, { operator: "-" })) return -ev(n.argument);
          if (t.isUnaryExpression(n, { operator: "+" })) return +ev(n.argument);
          if (t.isBinaryExpression(n)) {
            const a = ev(n.left), b = ev(n.right);
            switch (n.operator) {
              case "+": return a + b;
              case "-": return a - b;
              case "*": return a * b;
              case "/": return a / b;
              case "%": return a % b;
            }
            throw new Error("operator " + n.operator);
          }
          if (t.isParenthesizedExpression(n)) return ev(n.expression);
          const v = evalConst(n);
          if (!v) throw new Error("unsupported node " + n.type);
          return v.v;
        };
        return ev(expr.node);
      };
      let rot = values.slice();
      let found = null;
      for (let k = 0; k <= values.length; k++) {
        let v;
        let threw = false;
        try {
          v = evalWith(rot);
        } catch (e) {
          if (process.env.OBFIODBG && k < 4) console.error("OBFIODBG threw", e.message);
          if (/unresolvable|non-constant|unsupported|operator|another array/.test(e.message)) {
            if (process.env.OBFIODBG) console.error("OBFIODBG rotation:", e.message);
            return; // shape we don't model
          }
          threw = true; // decoder error -> the template rotates again
        }
        if (process.env.OBFIODBG && k < 4) console.error("OBFIODBG k", k, "value", threw ? "threw" : v, "target", target.v);
        if (!threw && v === target.v) {
          found = rot;
          break;
        }
        rot = rot.slice(1).concat(rot.slice(0, 1)); // push(shift())
      }
      if (!found) {
        if (process.env.OBFIODBG) console.error("OBFIODBG rotation not found");
        return;
      }
      unproven.delete(ab);
      rotation.set(ab, found);
      rotateIIFEs.set(ab, cp.parentPath.isExpressionStatement() ? cp.parentPath : cp);
    },
  });
  // arrays without a rotation loop are used as-is; never guess a rotation
  for (const [ab, a] of arrays) if (!rotation.has(ab) && !unproven.has(ab)) rotation.set(ab, a.values);
  if (unproven.size) ctx.errors.push(`obfuscator.io string array: rotation not proven for ${unproven.size} array(s); their strings left encoded`);

  /* 5. replace every resolvable call */
  const seenKeys = new Map(); // decoder+index -> key (rc4 caches per index, ignoring the key)
  const sites = [];
  let failed = 0;
  traverse(ast, {
    CallExpression(cp) {
      const c = cp.node;
      if (!t.isIdentifier(c.callee)) return;
      if (rotateIIFEs.size && [...rotateIIFEs.values()].some((r) => cp.isDescendant(r))) return;
      const b = cp.scope.getBinding(c.callee.name);
      if (!b) return;
      const res = resolverOf(b);
      if (!res) return;
      if (decoders.has(b) && [...decoders.values()].some((d) => cp.isDescendant(d.path))) return;
      const args = [];
      const lk = constObjectLookup(cp.scope);
      for (const a of c.arguments) {
        const v = evalConst(a, new Map(), lk);
        if (!v) return void failed++;
        args.push(v.v);
      }
      const r = res(args);
      if (!r) return void failed++;
      if (!rotation.has(r.info.arrBinding)) return; // rotation unproven: leave it
      const index = Number(r.index);
      const ck = r.info.path.node.id.name + "|" + (index - r.info.shift);
      if (r.info.kind === "rc4") {
        if (seenKeys.has(ck) && seenKeys.get(ck) !== String(r.key)) return void failed++;
        seenKeys.set(ck, String(r.key));
      }
      let v;
      try {
        v = decode(r.info, rotation.get(r.info.arrBinding), index, r.key);
      } catch {
        return void failed++;
      }
      if (typeof v !== "string") return void failed++;
      sites.push({ cp, v });
    },
  });
  for (const { cp, v } of sites) cp.replaceWith(t.stringLiteral(v));
  if (failed) ctx.errors.push(`obfuscator.io string array: ${failed} call(s) left (unresolved)`);

  /* 6. remove machinery nothing uses any more (rotation IIFEs first) */
  if (!failed) for (const r of rotateIIFEs.values()) if (!r.removed) r.remove();
  removeUnused(ast);
  return sites.length;
}

/** remove wrappers / aliases / decoders / arrays that are no longer referenced */
function removeUnused(ast) {
  for (let i = 0; i < 20; i++) {
    crawl(ast);
    let changed = false;
    traverse(ast, {
      "FunctionDeclaration|VariableDeclarator"(path) {
        const id = path.node.id;
        if (!t.isIdentifier(id)) return;
        const scope = path.isFunctionDeclaration() ? path.parentPath.scope : path.scope;
        const b = scope.getBinding(id.name);
        if (!b || b.path.node !== path.node) return;
        // self-references (the array function reassigning/calling itself) don't keep it alive
        const owner = path.isFunctionDeclaration() ? path : path.get("init");
        const outside = b.referencePaths.filter((r) => !(owner.node && r.isDescendant(owner)));
        if (outside.length) return;
        const outsideWrites = b.constantViolations.filter((cv) => cv.node !== path.node && !(owner.node && cv.isDescendant(owner)));
        // only obfuscator machinery shapes: function decls, `var x = <identifier>`, `var x = function`
        if (path.isVariableDeclarator()) {
          const init = path.node.init;
          if (!(t.isIdentifier(init) || t.isFunctionExpression(init))) return;
          if (outsideWrites.length) return;
          if (path.parent.declarations.length === 1) path.parentPath.remove();
          else path.remove();
        } else {
          // function: only if it is string-array machinery-ish (no side effects when unused anyway)
          if (outsideWrites.length) return;
          path.remove();
        }
        changed = true;
      },
    });
    if (!changed) break;
  }
}

/* ======================================== self-defending / labels */
/**
 * SelfDefendingTemplate:
 *   const S = CC(this, function () {
 *     if (S.bind().toString().indexOf('\n') !== -1) return;
 *     return S.toString().search('(((.+)+)+)+$').toString().constructor(S).search('(((.+)+)+)+$');
 *   });
 *   S();
 * On the untouched (one-line) program it has no effect; once the code is
 * reformatted the regex backtracks catastrophically and hangs. So it is
 * removed — required for the readable output to run at all.
 * ConsoleOutputDisableTemplate / DebugProtection really change behaviour:
 * they are kept and labelled with a comment.
 */
export function cleanObfioHelpers(ast, ctx) {
  crawl(ast);
  let selfDefending = 0;
  let labelled = 0;
  traverse(ast, {
    VariableDeclarator(path) {
      const d = path.node;
      if (!t.isIdentifier(d.id) || !t.isCallExpression(d.init) || d.init.arguments.length !== 2) return;
      const [ctxArg, fnArg] = d.init.arguments;
      if (!t.isThisExpression(ctxArg) || !t.isFunctionExpression(fnArg)) return;
      const text = nodeText(fnArg.body);
      const declStmt = path.parentPath;
      if (!Array.isArray(declStmt.container)) return;
      const next = declStmt.container[declStmt.key + 1];
      const isSelfCall = (st) =>
        t.isExpressionStatement(st) && t.isCallExpression(st.expression) && t.isIdentifier(st.expression.callee, { name: d.id.name }) && st.expression.arguments.length === 0;
      // structural: only `if (<guard>) return;` and `return <…search…>` statements
      // (dead-code injection can copy the regex string into other helpers,
      // e.g. the disableConsoleOutput wrapper, which must be kept)
      const sdShape = fnArg.body.body.length >= 1 && fnArg.body.body.every((st) =>
        t.isReturnStatement(st) ||
        (t.isIfStatement(st) && !st.alternate && (t.isReturnStatement(st.consequent) || (t.isBlockStatement(st.consequent) && st.consequent.body.length === 1 && t.isReturnStatement(st.consequent.body[0])))));
      const last = fnArg.body.body[fnArg.body.body.length - 1];
      if (sdShape && t.isReturnStatement(last) && last.argument && nodeText(last.argument).includes("(((.+)+)+)+$") && text.includes('"search"') && !text.includes('"console"')) {
        const b = path.scope.getBinding(d.id.name);
        if (!b || b.constantViolations.length) return;
        // uses: inside its own function, plus the single `S();`
        const outside = b.referencePaths.filter((r) => !r.isDescendant(path.get("init.arguments.1")));
        if (outside.length !== 1 || !isSelfCall(next) || outside[0].node !== next.expression.callee) return;
        declStmt.container.splice(declStmt.key + 1, 1);
        if (declStmt.node.declarations.length === 1) declStmt.remove();
        else path.remove();
        selfDefending++;
        return;
      }
      const consoleNames = ["log", "warn", "info", "error", "exception", "table", "trace"];
      if (consoleNames.every((n) => text.includes(`"value":"${n}"`)) && text.includes('"console"')) {
        if (!declStmt.node.leadingComments?.some((c) => c.value.includes("obfuscator.io"))) {
          t.addComment(declStmt.node, "leading", " obfuscator.io disableConsoleOutput: after its first run console.log/warn/info/error/… do nothing (kept: it changes behaviour) ", false);
          labelled++;
        }
      }
    },
  });
  // debugProtection: kept (it changes behaviour under a debugger) but labelled
  const label = (node, text) => {
    if ((node.leadingComments || []).some((c) => c.value.includes("obfuscator.io debugProtection"))) return;
    t.addComment(node, "leading", ` obfuscator.io debugProtection: ${text} (kept: it changes behaviour) `, false);
    labelled++;
  };
  traverse(ast, {
    FunctionDeclaration(path) {
      const text = nodeText(path.node.body);
      if (text.includes('"debugger"') && text.includes('"counter"') && text.includes('"stateObject"'))
        label(path.node, "re-enters `debugger` forever while devtools are open"), path.skip();
    },
    ExpressionStatement(path) {
      if (!path.parentPath.isProgram() && !path.parentPath.isBlockStatement()) return;
      const text = nodeText(path.node);
      if (text.includes("setInterval") && text.includes("return this") && t.isCallExpression(path.node.expression)) label(path.node, "re-arms the debugger trap every 4 s"), path.skip();
      else if (text.includes('"init"') && text.includes('"chain"') && text.includes('"input"')) label(path.node, "starts the debugger trap"), path.skip();
    },
  });
  if (selfDefending || labelled) ctx.stats.obfioHelpers = { selfDefending, labelled };
}

/* ================================================= structural passes */
/**
 * - dead code injection: `if ("abc" === "xyz") {A} else {B}` → the live block
 * - transformObjectKeys: `var o = {}; o.a = 1; o.b = f;` → `var o = { a: 1, b: f };`
 * - control-flow storage: o = { k: function (x, y) { return x + y; }, s: "str",
 *   c: function (callee, a) { return callee(a); } } → inline `o.k(a, b)` etc.
 * - block flattening: { const C = "1|0|2".split("|"); let i = 0;
 *     while (true) { switch (C[i++]) { case "0": S0; continue; … } break; } }
 * - numbersToExpressions (only when obfuscator.io was detected): fold literal arithmetic
 */
const pureArg = (n) =>
  t.isIdentifier(n) || t.isLiteral(n) && !t.isTemplateLiteral(n) ||
  (t.isUnaryExpression(n) && ["-", "+", "!"].includes(n.operator) && t.isLiteral(n.argument));

export function reverseObfioStructure(ast, ctx, { foldNumbers = false } = {}) {
  const stats = { deadCode: 0, objectKeys: 0, storage: 0, blocks: 0, numbers: 0 };
  crawl(ast);

  /* --- dead code: literal string comparisons */
  traverse(ast, {
    "IfStatement|ConditionalExpression": {
      exit(p) {
        const test = p.node.test;
        if (!t.isBinaryExpression(test) || !["===", "!==", "==", "!="].includes(test.operator)) return;
        if (!t.isStringLiteral(test.left) || !t.isStringLiteral(test.right)) return;
        const v = evalConst(test).v;
        const branch = v ? p.node.consequent : p.node.alternate;
        if (p.isConditionalExpression()) return void p.replaceWith(branch);
        if (!branch) return void p.remove();
        p.replaceWith(branch);
        stats.deadCode++;
      },
    },
  });

  /* --- transformObjectKeys: merge `o.k = v;` statements right after `var o = {}` */
  crawl(ast);
  traverse(ast, {
    VariableDeclaration(path) {
      if (path.node.declarations.length !== 1) return;
      const d = path.node.declarations[0];
      if (!t.isIdentifier(d.id) || !t.isObjectExpression(d.init)) return;
      if (!Array.isArray(path.container)) return;
      const list = path.container;
      let i = path.key + 1;
      const merged = [];
      while (i < list.length) {
        const st = list[i];
        if (!t.isExpressionStatement(st) || !t.isAssignmentExpression(st.expression, { operator: "=" })) break;
        const left = st.expression.left;
        if (!t.isMemberExpression(left) || !t.isIdentifier(left.object, { name: d.id.name })) break;
        const key = memberKey(left);
        if (key === null || key === "__proto__") break;
        // the value must not read the object being built
        let reads = false;
        traverse(t.file(t.program([t.expressionStatement(t.cloneNode(st.expression.right, true))])), { noScope: true, Identifier(ip) { if (ip.node.name === d.id.name) reads = true; } });
        if (reads || t.isIdentifier(st.expression.right, { name: d.id.name })) break;
        merged.push(t.objectProperty(t.isValidIdentifier(key) ? t.identifier(key) : t.stringLiteral(key), st.expression.right));
        i++;
      }
      if (!merged.length) return;
      // keys may not repeat an existing literal key with a getter/setter
      if (d.init.properties.some((pp) => !t.isObjectProperty(pp))) return;
      d.init.properties.push(...merged);
      list.splice(path.key + 1, merged.length);
      stats.objectKeys += merged.length;
    },
  });

  /* --- control-flow storage objects
     Several objects per traversal; a site whose path went stale (it sat inside
     a call another object's inlining replaced) skips its object until the next
     pass, which re-crawls. */
  const attached = (p) => {
    for (let q = p; q && !q.isProgram(); q = q.parentPath) {
      if (q.removed || !q.container) return false;
      const at = q.listKey ? q.container[q.key] : q.container[q.key];
      if (at !== q.node) return false;
    }
    return true;
  };
  for (let pass = 0, changed = true; changed && pass < 64; pass++) {
  changed = false;
  crawl(ast);
  traverse(ast, {
    VariableDeclarator(path) {
      const d = path.node;
      if (!t.isIdentifier(d.id) || !t.isObjectExpression(d.init) || !d.init.properties.length) return;
      const b = path.scope.getBinding(d.id.name);
      if (!b || b.path !== path) return;
      // writes to the binding are escapes: allowed only in proven-dead branches
      // entries: function (params) { return <expr>; } or a string literal
      const entries = new Map();
      const entryNodes = new Map();
      for (const pp of d.init.properties) {
        if (!t.isObjectProperty(pp) || pp.computed && !t.isStringLiteral(pp.key)) return;
        const k = t.isIdentifier(pp.key) ? pp.key.name : t.isStringLiteral(pp.key) ? pp.key.value : null;
        if (k === null || entries.has(k)) return;
        const v = pp.value;
        entryNodes.set(k, v);
        if (t.isStringLiteral(v)) entries.set(k, { lit: v.value });
        else if (t.isFunctionExpression(v) && v.params.every((x) => t.isIdentifier(x) || (t.isRestElement(x) && t.isIdentifier(x.argument))) && v.body.body.length === 1 && t.isReturnStatement(v.body.body[0]) && v.body.body[0].argument) {
          entries.set(k, { fn: v });
        } else return;
      }
      // aliases: var c = o;  every use of o / aliases must be o.k / o.k(...)
      const groups = [b];
      for (const r of b.referencePaths) {
        if (r.parentPath.isVariableDeclarator() && r.key === "init" && t.isIdentifier(r.parent.id)) {
          const ab = r.parentPath.scope.getBinding(r.parent.id.name);
          if (!ab || ab.constantViolations.length) return;
          groups.push(ab);
        }
      }
      const sites = [];
      const escapes = [...b.constantViolations]; // + references that are not a plain read / call of an entry
      const groupBindings = new Set(groups);
      for (const g of groups)
        for (const r of g.referencePaths) {
          if (g === b && r.parentPath.isVariableDeclarator() && r.key === "init") continue; // alias decl
          const mp = r.parentPath;
          if (!mp.isMemberExpression() || r.key !== "object") { escapes.push(r); continue; }
          const k = memberKey(mp.node);
          const e = k === null ? null : entries.get(k);
          if (!e) { escapes.push(r); continue; }
          if ((mp.parentPath.isAssignmentExpression() && mp.key === "left") || mp.parentPath.isUpdateExpression() || mp.parentPath.isUnaryExpression({ operator: "delete" })) { escapes.push(r); continue; }
          if (e.fn && !(mp.parentPath.isCallExpression() && mp.key === "callee")) { escapes.push(r); continue; }
          sites.push({ mp, e });
        }
      // Escaping references are allowed only inside branches the storage itself
      // proves dead. Sound by induction: the object cannot change before some
      // escape runs, and every escape sits behind a test that - evaluated with
      // the unchanged object - never selects it.
      if (escapes.length) {
        // Evaluates a guard test reading this object or any other storage-shaped
        // object that is never written and never escapes (so it is unchanged too).
        const escapesQueue = escapes.slice();
        const pending = escapesQueue;
        const views = new Map();
        const viewOf = (vb) => {
          if (groupBindings.has(vb)) return { props: entryNodes, scope: path.scope };
          if (!vb || views.has(vb)) return views.get(vb) || null;
          views.set(vb, null);
          const init = vb.path.isVariableDeclarator() ? vb.path.node.init : null;
          if (!t.isObjectExpression(init)) return null;
          const props = new Map();
          for (const pp of init.properties) {
            if (!t.isObjectProperty(pp) || (pp.computed && !t.isStringLiteral(pp.key))) return null;
            const k = t.isIdentifier(pp.key) ? pp.key.name : t.isStringLiteral(pp.key) ? pp.key.value : null;
            if (k === null || props.has(k)) return null;
            props.set(k, pp.value);
          }
          const own = [];
          for (const r of vb.referencePaths) {
            const mp = r.parentPath;
            if (mp.isMemberExpression() && r.key === "object" &&
              ((mp.parentPath.isAssignmentExpression() && mp.key === "left") || mp.parentPath.isUpdateExpression() || mp.parentPath.isUnaryExpression({ operator: "delete" })))
              return null; // written directly: never a view
            if (!mp.isMemberExpression() || r.key !== "object" || !props.has(memberKey(mp.node))) own.push(r);
          }
          // its escapes and writes join the proof obligation (joint induction over all views)
          for (const r of own) pending.push(r);
          for (const w of vb.constantViolations) pending.push(w);
          const v = { props, scope: vb.path.scope };
          views.set(vb, v);
          return v;
        };
        const lit = (v) => (v === undefined ? t.identifier("undefined") : t.valueToNode(v));
        const evalTest = (n, sc, env = new Map(), depth = 0) => {
          if (depth > 24) return null;
          if (t.isIdentifier(n) && env.has(n.name)) return { v: env.get(n.name) };
          if (t.isMemberExpression(n) && t.isIdentifier(n.object) && !env.has(n.object.name)) {
            const view = viewOf(sc.getBinding(n.object.name));
            const vn = view && view.props.get(memberKey(n));
            if (!vn || t.isFunction(vn)) return null;
            return evalTest(vn, view.scope, new Map(), depth + 1);
          }
          if (t.isCallExpression(n) && t.isMemberExpression(n.callee) && t.isIdentifier(n.callee.object) && !env.has(n.callee.object.name)) {
            const view = viewOf(sc.getBinding(n.callee.object.name));
            const fn = view && view.props.get(memberKey(n.callee));
            if (!t.isFunctionExpression(fn) || fn.params.some((x) => !t.isIdentifier(x)) || fn.params.length !== n.arguments.length) return null;
            if (fn.body.body.length !== 1 || !t.isReturnStatement(fn.body.body[0]) || !fn.body.body[0].argument) return null;
            const env2 = new Map();
            for (let i = 0; i < n.arguments.length; i++) {
              const v = evalTest(n.arguments[i], sc, env, depth + 1);
              if (!v) return null;
              env2.set(fn.params[i].name, v.v);
            }
            return evalTest(fn.body.body[0].argument, view.scope, env2, depth + 1);
          }
          if (t.isUnaryExpression(n) && ["!", "-", "+", "typeof", "void", "~"].includes(n.operator)) {
            const v = evalTest(n.argument, sc, env, depth + 1);
            return v ? evalConst(t.unaryExpression(n.operator, lit(v.v))) : null;
          }
          if (t.isBinaryExpression(n)) {
            const x = evalTest(n.left, sc, env, depth + 1);
            if (!x) return null;
            const y = evalTest(n.right, sc, env, depth + 1);
            if (!y) return null;
            return evalConst(t.binaryExpression(n.operator, lit(x.v), lit(y.v)));
          }
          if (t.isLiteral(n) && !t.isTemplateLiteral(n) && !t.isRegExpLiteral(n)) return evalConst(n);
          return null;
        };
        const provenDead = (r) => {
          for (let c = r, q = r.parentPath; q; c = q, q = q.parentPath) {
            if ((q.isIfStatement() || q.isConditionalExpression()) && (c.key === "consequent" || c.key === "alternate")) {
              const v = evalTest(q.node.test, q.scope);
              if (v && !!v.v === (c.key === "alternate")) return true;
            }
            if (q === path) return false;
          }
          return false;
        };
        // every escape of this object and of every object a guard read through
        // must be proven dead (the list grows as guards discover new views)
        for (let i = 0; i < pending.length; i++) if (i > 2000 || !provenDead(pending[i])) return;
      }
      // validate every site first (bail on the whole object if any is unsafe),
      // then rewrite innermost-first so nested storage calls stay valid
      const buildFor = (mp, e, dry = false) => {
        if (e.lit !== undefined) return dry ? true : { target: mp, node: t.stringLiteral(e.lit) };
        const call = mp.parentPath.node;
        const fn = e.fn;
        const params = fn.params.map((x) => (t.isRestElement(x) ? x.argument.name : x.name));
        const hasRest = fn.params.some((x) => t.isRestElement(x));
        const body = fn.body.body[0].argument;
        // each param used exactly once, in order, and nothing else free
        const uses = [];
        let other = false;
        traverse(t.file(t.program([t.expressionStatement(t.cloneNode(body, true))])), {
          noScope: true,
          Identifier(ip) {
            if (ip.parentPath.isMemberExpression() && ip.key === "property" && !ip.parent.computed) return;
            if (params.includes(ip.node.name)) uses.push(ip.node.name);
            else other = true;
          },
          Function() {
            other = true;
          },
          ThisExpression() {
            other = true;
          },
        });
        if (other || uses.length !== params.length || uses.some((u, i) => u !== params[i])) return null;
        const args = call.arguments;
        if (hasRest) {
          if (args.length < params.length - 1) return null;
        } else if (args.length !== params.length || args.some((a) => t.isSpreadElement(a))) return null;
        if (t.isLogicalExpression(body) && !args.every(pureArg)) return null; // storage evaluated both eagerly
        if (dry) return true; // validation never touches the real argument nodes
        const map = new Map();
        params.forEach((pn, i) => {
          if (hasRest && i === params.length - 1) map.set(pn, { spread: args.slice(i) });
          else map.set(pn, args[i]);
        });
        // substitute without NodePaths: traversing a holder over the real
        // argument nodes would re-parent Babel's cached child paths
        let bad = false;
        const subst = (node, parent, key) => {
          if (t.isIdentifier(node)) {
            if ((t.isMemberExpression(parent) || t.isOptionalMemberExpression(parent)) && key === "property" && !parent.computed) return node;
            if (t.isObjectProperty(parent) && key === "key" && !parent.computed) return node;
            const rep = map.get(node.name);
            if (rep === undefined) return node;
            if (rep.spread) return void (bad = true), node;
            if ((t.isCallExpression(parent) || t.isOptionalCallExpression(parent)) && key === "callee" && (t.isMemberExpression(rep) || t.isOptionalMemberExpression(rep)))
              return t.sequenceExpression([t.numericLiteral(0), rep]);
            return rep;
          }
          for (const k of t.VISITOR_KEYS[node.type] || []) {
            const v = node[k];
            if (Array.isArray(v)) {
              const out = [];
              for (const c of v) {
                if (!c) out.push(c);
                else if (t.isSpreadElement(c) && t.isIdentifier(c.argument) && map.get(c.argument.name)?.spread) out.push(...map.get(c.argument.name).spread);
                else out.push(subst(c, node, k));
              }
              node[k] = out;
            } else if (v && typeof v === "object" && v.type) node[k] = subst(v, node, k);
          }
          return node;
        };
        const result = subst(t.cloneNode(body, true), null, null);
        if (bad) return null;
        return { target: mp.parentPath, node: result };
      };
      if (!sites.length) return;
      for (const { mp, e } of sites) if (!buildFor(mp, e, true)) return; // validation only
      for (const { mp } of sites) if (!attached(mp)) return void (changed = true); // stale: next pass
      // depth of the node actually replaced (a call site replaces its CallExpression)
      const depth = ({ mp, e }) => (e.lit !== undefined ? mp : mp.parentPath).getAncestry().length;
      const ordered = sites.slice().sort((x, y) => depth(y) - depth(x));
      const plans = [];
      for (const { mp, e } of ordered) {
        const pl = buildFor(mp, e);
        if (!pl) return;
        pl.target.replaceWith(pl.node);
        plans.push(pl);
      }
      stats.storage += plans.length;
      changed = true;
    },
  });
  }

  /* --- block flattening */
  traverse(ast, {
    BlockStatement(p) {
      const body = p.node.body;
      if (body.length !== 3) return;
      const [ctl, idx, loop] = body;
      if (!t.isVariableDeclaration(ctl) || ctl.declarations.length !== 1 || !t.isIdentifier(ctl.declarations[0].id)) return;
      const init = ctl.declarations[0].init;
      if (!t.isCallExpression(init) || !t.isMemberExpression(init.callee) || memberKey(init.callee) !== "split" || !t.isStringLiteral(init.callee.object) || init.arguments.length !== 1 || !t.isStringLiteral(init.arguments[0], { value: "|" })) return;
      const order = init.callee.object.value.split("|");
      if (!t.isVariableDeclaration(idx) || idx.declarations.length !== 1 || !t.isIdentifier(idx.declarations[0].id) || evalConst(idx.declarations[0].init)?.v !== 0) return; // 0, or 0 rewritten by numbersToExpressions
      if (!t.isWhileStatement(loop) || !(t.isBooleanLiteral(loop.test, { value: true }) || (t.isUnaryExpression(loop.test, { operator: "!" }) && t.isUnaryExpression(loop.test.argument, { operator: "!" })))) return;
      const lb = t.isBlockStatement(loop.body) ? loop.body.body : null;
      if (!lb || lb.length !== 2 || !t.isSwitchStatement(lb[0]) || !t.isBreakStatement(lb[1]) || lb[1].label) return;
      const sw = lb[0];
      const disc = sw.discriminant;
      const C = ctl.declarations[0].id.name;
      const I = idx.declarations[0].id.name;
      if (!t.isMemberExpression(disc, { computed: true }) || !t.isIdentifier(disc.object, { name: C }) || !t.isUpdateExpression(disc.property, { operator: "++", prefix: false }) || !t.isIdentifier(disc.property.argument, { name: I })) return;
      const byKey = new Map();
      for (const c of sw.cases) {
        if (!t.isStringLiteral(c.test) || byKey.has(c.test.value)) return;
        // one original statement (earlier passes may have split it into several)
        // followed by `continue`, or ending in `return`
        const cons = c.consequent;
        const last = cons[cons.length - 1];
        const isFlow = (x) => t.isContinueStatement(x) || t.isBreakStatement(x) || t.isReturnStatement(x);
        if (cons.length >= 2 && t.isContinueStatement(last) && !last.label && !cons.slice(0, -1).some(isFlow)) byKey.set(c.test.value, { stmts: cons.slice(0, -1), ret: false });
        else if (cons.length >= 1 && t.isReturnStatement(last) && !cons.slice(0, -1).some(isFlow)) byKey.set(c.test.value, { stmts: cons, ret: true });
        else return;
      }
      if (order.length !== byKey.size || !order.every((k) => byKey.has(k))) return;
      // C and I must not be used by the statements themselves
      let leaks = false;
      for (const c of sw.cases)
        traverse(t.file(t.program(c.consequent.map((x) => t.cloneNode(x, true)))), { noScope: true, Identifier(ip) { if (ip.node.name === C || ip.node.name === I) leaks = true; } });
      if (leaks) return;
      const stmts = [];
      for (const k of order) {
        const e = byKey.get(k);
        stmts.push(...e.stmts);
        if (e.ret) break; // the original block ended with this return
      }
      p.node.body = stmts;
      stats.blocks++;
    },
  });

  /* --- numbersToExpressions */
  if (foldNumbers)
    traverse(ast, {
      BinaryExpression: {
        exit(p) {
          if (!["+", "-", "*"].includes(p.node.operator)) return;
          const isNum = (n) => t.isNumericLiteral(n) || (t.isUnaryExpression(n, { operator: "-" }) && t.isNumericLiteral(n.argument));
          if (!isNum(p.node.left) || !isNum(p.node.right)) return;
          const v = evalConst(p.node);
          if (!v || typeof v.v !== "number" || !Number.isFinite(v.v)) return;
          p.replaceWith(v.v < 0 || Object.is(v.v, -0) ? t.unaryExpression("-", t.numericLiteral(-v.v)) : t.numericLiteral(v.v));
          stats.numbers++;
        },
      },
    });

  /* --- bare nested blocks `{ { ... } }` (left by block flattening / dead-code
     removal): unwrap when the inner block declares nothing block-scoped */
  traverse(ast, {
    BlockStatement: {
      exit(p) {
        if (!(p.parentPath.isBlockStatement() || p.parentPath.isProgram())) return;
        const lexical = p.node.body.some((st) => t.isFunctionDeclaration(st) || t.isClassDeclaration(st) || (t.isVariableDeclaration(st) && st.kind !== "var"));
        if (lexical || (p.node.directives && p.node.directives.length)) return;
        if (p.node.body.length) p.replaceWithMultiple(p.node.body);
        else p.remove();
        stats.blocks++;
      },
    },
  });

  const any = Object.values(stats).some(Boolean);
  if (any) ctx.stats.obfioStructure = stats;
}
