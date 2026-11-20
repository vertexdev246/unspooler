/**
 * Reverse JS-Confuser Control Flow Flattening (dist/transforms/controlFlowFlattening.js).
 *
 * Shape: per flattened program/function
 *   function MAIN(states, scope = {"P": {}}, runtime, arg) {
 *     while (SUM(states) !== END) switch (SUM(states)) { case …: <block> }
 *   }
 * plus program-level helpers SUM(array), SLICE(min, max) over a SEQUENCE
 * number array, XOR(key, start, length) over a STRINGS blob.
 *
 * Every basic block has a fixed state vector, so following the real jumps
 * from each entry vector visits exactly the live blocks, and every
 * `states[k]` inside a block is a known constant. That folds the mangled
 * numbers / booleans / strings, removes fake blocks and fake jumps, and
 * gives a DAG of blocks that is restructured into statements + if/else.
 *
 * Anything that doesn't match exactly makes the machine stay untouched
 * (reason pushed to ctx.errors): no guessing.
 */
import * as t from "@babel/types";
const require = (await import("module")).createRequire(import.meta.url);
const traverse = require("@babel/traverse").default;
const generate = require("@babel/generator").default;

class Bail extends Error {}
/** `return;` / `return undefined;` / `return void 0;` — same as falling off the end */
const isEmptyReturn = (st) =>
  t.isReturnStatement(st) &&
  (!st.argument ||
    t.isIdentifier(st.argument, { name: "undefined" }) ||
    (t.isUnaryExpression(st.argument, { operator: "void" }) && t.isNumericLiteral(st.argument.argument)));
function cycleCheck(root, tag) {
  if (!process.env.CFFDBG) return;
  console.error("checkpoint", tag);
  const onPath = new Set();
  const visit = (n) => {
    if (!n || typeof n !== "object") return;
    if (Array.isArray(n)) return n.forEach(visit);
    if (typeof n.type !== "string") return;
    if (onPath.has(n)) throw new Error("AST cycle after " + tag + " at " + n.type);
    onPath.add(n);
    for (const k of Object.keys(n)) if (!["loc", "start", "end", "extra", "leadingComments", "trailingComments", "innerComments"].includes(k)) visit(n[k]);
    onPath.delete(n);
  };
  visit(root);
}
const bail = (msg) => {
  throw new Bail(msg);
};

/* ------------------------------------------------------------ helpers */
function numValue(n) {
  if (t.isNumericLiteral(n)) return n.value;
  if (t.isUnaryExpression(n, { operator: "-" }) && t.isNumericLiteral(n.argument)) return -n.argument.value;
  return null;
}
function literalOf(v) {
  if (typeof v === "boolean") return t.booleanLiteral(v);
  if (typeof v === "number") {
    if (Object.is(v, -0)) return t.unaryExpression("-", t.numericLiteral(0));
    return v < 0 ? t.unaryExpression("-", t.numericLiteral(-v)) : t.numericLiteral(v);
  }
  if (typeof v === "string") return t.stringLiteral(v);
  return null;
}
const propKey = (n) =>
  t.isStringLiteral(n) ? n.value : null;
const memberKey = (m) =>
  m.computed ? propKey(m.property) : t.isIdentifier(m.property) ? m.property.name : null;

/** decode exactly like xorDecodeStringTemplate */
function xorDecode(blob, key, start, length) {
  let result = "";
  for (let i = 0; i < length; i++) {
    key = (key + 0x9e3779b9) | 0;
    const ks = (((key ^ (key >>> 13)) % 95) + 95) % 95;
    const normalized = blob.charCodeAt(start + i) - 32;
    const shifted = (((normalized - ks) % 95) + 95) % 95;
    result += String.fromCharCode(shifted + 32);
  }
  return result;
}

/* ------------------------------------------------- program helpers */
function findHelpers(programPath) {
  const scope = programPath.scope;
  const helpers = { sum: null, slice: null, sequence: null, xor: null, strings: null };

  const constValue = (name) => {
    const b = scope.getBinding(name);
    if (!b || b.constantViolations.length > 1) return null;
    let init = null;
    if (b.path.isVariableDeclarator()) init = b.path.node.init;
    if (!init && b.constantViolations.length === 1) {
      const cv = b.constantViolations[0];
      if (cv.isAssignmentExpression({ operator: "=" })) init = cv.node.right;
    } else if (b.constantViolations.length) return null;
    return { binding: b, init };
  };

  for (const sp of programPath.get("body")) {
    if (!sp.isFunctionDeclaration() || !sp.node.id) continue;
    const fn = sp.node;
    const body = fn.body.body;
    // SUM(array): for (var sum = 0, i = 0; i < array.length; i++) sum += array[i]; return sum;
    if (fn.params.length === 1 && t.isIdentifier(fn.params[0]) && body.length === 2 && t.isForStatement(body[0]) && t.isReturnStatement(body[1])) {
      const a = fn.params[0].name;
      const f = body[0];
      const init = f.init;
      const ret = body[1].argument;
      const inner = t.isBlockStatement(f.body) ? (f.body.body.length === 1 ? f.body.body[0] : null) : f.body;
      if (
        t.isVariableDeclaration(init) &&
        init.declarations.length === 2 &&
        init.declarations.every((d) => t.isIdentifier(d.id) && numValue(d.init) === 0) &&
        t.isIdentifier(ret, { name: init.declarations[0].id.name }) &&
        t.isBinaryExpression(f.test, { operator: "<" }) &&
        t.isIdentifier(f.test.left, { name: init.declarations[1].id.name }) &&
        t.isMemberExpression(f.test.right) &&
        t.isIdentifier(f.test.right.object, { name: a }) &&
        memberKey(f.test.right) === "length" &&
        t.isUpdateExpression(f.update, { operator: "++" }) &&
        t.isExpressionStatement(inner) &&
        t.isAssignmentExpression(inner.expression, { operator: "+=" }) &&
        t.isIdentifier(inner.expression.left, { name: init.declarations[0].id.name }) &&
        t.isMemberExpression(inner.expression.right, { computed: true }) &&
        t.isIdentifier(inner.expression.right.object, { name: a }) &&
        t.isIdentifier(inner.expression.right.property, { name: init.declarations[1].id.name })
      )
        helpers.sum = scope.getBinding(fn.id.name);
      continue;
    }
    // SLICE(min, max): return SEQUENCE.slice(min, max)
    if (fn.params.length === 2 && body.length === 1 && t.isReturnStatement(body[0])) {
      const r = body[0].argument;
      if (
        t.isCallExpression(r) &&
        t.isMemberExpression(r.callee) &&
        memberKey(r.callee) === "slice" &&
        t.isIdentifier(r.callee.object) &&
        r.arguments.length === 2 &&
        r.arguments.every((x, i) => t.isIdentifier(x, { name: fn.params[i].name }))
      ) {
        const cv = constValue(r.callee.object.name);
        if (cv && t.isArrayExpression(cv.init) && cv.init.elements.every((e) => numValue(e) !== null)) {
          helpers.slice = scope.getBinding(fn.id.name);
          helpers.sequence = { binding: cv.binding, values: cv.init.elements.map(numValue) };
        }
      }
      continue;
    }
    // XOR(key, start, length) over STRINGS
    if (fn.params.length === 3) {
      const code = JSON.stringify(fn.body, (k, v) => (k === "loc" || k === "start" || k === "end" || k === "extra" ? undefined : v));
      if (!/"value":2654435769/.test(code) || !/"value":95/.test(code) || !/"value":13/.test(code)) continue;
      let blobName = null;
      traverse(fn.body, {
        noScope: true,
        MemberExpression(p) {
          if (memberKey(p.node) === "charCodeAt" && t.isIdentifier(p.node.object)) blobName = p.node.object.name;
        },
      });
      if (!blobName) continue;
      const cv = constValue(blobName);
      if (cv && t.isStringLiteral(cv.init)) {
        helpers.xor = scope.getBinding(fn.id.name);
        helpers.strings = { binding: cv.binding, value: cv.init.value };
      }
    }
  }
  return helpers;
}

/* ------------------------------------------------ machine detection */
function machineOf(fnPath, helpers) {
  const fn = fnPath.node;
  if (!helpers.sum) return null;
  if (fn.params.length < 2 || !t.isIdentifier(fn.params[0])) return null;
  const scopeParam = fn.params[1];
  if (!t.isAssignmentPattern(scopeParam) || !t.isIdentifier(scopeParam.left) || !t.isObjectExpression(scopeParam.right)) return null;
  const body = fn.body.body;
  if (!t.isWhileStatement(body[0]) || !(body.length === 1 || (body.length === 2 && isEmptyReturn(body[1])))) return null;
  const w = body[0];
  const S = fn.params[0].name;
  const isSum = (e) =>
    t.isCallExpression(e) &&
    t.isIdentifier(e.callee) &&
    fnPath.scope.getBinding(e.callee.name) === helpers.sum &&
    e.arguments.length === 1 &&
    t.isIdentifier(e.arguments[0], { name: S });
  if (!t.isBinaryExpression(w.test, { operator: "!==" }) || !isSum(w.test.left)) return null;
  const END = numValue(w.test.right);
  if (END === null) return null;
  let sw = t.isBlockStatement(w.body) ? (w.body.body.length === 1 ? w.body.body[0] : null) : w.body;
  let label = null;
  if (t.isLabeledStatement(sw)) {
    label = sw.label.name;
    sw = sw.body;
  }
  if (!t.isSwitchStatement(sw) || !isSum(sw.discriminant)) return null;
  return {
    fnPath,
    name: fn.id ? fn.id.name : null,
    S,
    scopeName: scopeParam.left.name,
    runtimeName: t.isIdentifier(fn.params[2]) ? fn.params[2].name : null,
    argName: t.isIdentifier(fn.params[3]) ? fn.params[3].name : null,
    defaultScope: scopeParam.right,
    END,
    label,
    switchNode: sw,
  };
}

/* ----------------------------------------------------- evaluation */
/** evaluate an expression built only from numbers, states[k] and operators */
function makeEval(m, statesBindingOf) {
  function ev(n, V, scopeOf) {
    if (t.isNumericLiteral(n)) return n.value;
    if (t.isBooleanLiteral(n)) return n.value;
    if (t.isParenthesizedExpression(n)) return ev(n.expression, V, scopeOf);
    if (t.isUnaryExpression(n)) {
      const a = ev(n.argument, V, scopeOf);
      if (a === undefined) return undefined;
      if (n.operator === "-") return -a;
      if (n.operator === "+") return +a;
      if (n.operator === "!") return !a;
      return undefined;
    }
    if (t.isMemberExpression(n, { computed: true }) && t.isIdentifier(n.object, { name: m.S }) && statesBindingOf(n.object)) {
      const k = ev(n.property, V, scopeOf);
      if (!Number.isInteger(k) || k < 0 || k >= V.length) return undefined;
      return V[k];
    }
    if (t.isBinaryExpression(n)) {
      const a = ev(n.left, V, scopeOf);
      if (a === undefined) return undefined;
      const b = ev(n.right, V, scopeOf);
      if (b === undefined) return undefined;
      switch (n.operator) {
        case "+": return a + b;
        case "-": return a - b;
        case "*": return a * b;
        case "==": return a == b; // eslint-disable-line eqeqeq
        case "!=": return a != b; // eslint-disable-line eqeqeq
        case "===": return a === b;
        case "!==": return a !== b;
        case "<": return a < b;
        case ">": return a > b;
        case "<=": return a <= b;
        case ">=": return a >= b;
      }
      return undefined;
    }
    if (t.isLogicalExpression(n)) {
      const a = ev(n.left, V, scopeOf);
      if (a === undefined) return undefined;
      if (n.operator === "&&") return a ? ev(n.right, V, scopeOf) : a;
      if (n.operator === "||") return a ? a : ev(n.right, V, scopeOf);
      return undefined;
    }
    return undefined;
  }
  return ev;
}

/* ------------------------------------------------- the reversal */
export function reverseControlFlowFlattening(ast, ctx) {
  let total = 0;
  for (let round = 0; round < 60; round++) {
    const n = reverseOneRound(ast, ctx);
    if (!n) break;
    total += n;
  }
  if (total) {
    ctx.stats.controlFlowFlattening = { machines: total, helpersRemoved: removeDeadHelpers(ast) };
  }
}

/** drop CFF helpers (sum, slice, sequence, xor, strings, hash) nothing uses any more */
function removeDeadHelpers(ast) {
  const programPath = crawl(ast);
  const h = findHelpers(programPath);
  const cands = [];
  const add = (b) => {
    if (b && !cands.some((c) => c.binding === b)) cands.push({ binding: b });
  };
  add(h.sum);
  add(h.slice);
  add(h.xor);
  if (h.sequence) add(h.sequence.binding);
  if (h.strings) add(h.strings.binding);
  // hash function (only used by CFF assertions)
  for (const sp of programPath.get("body")) {
    if (!sp.isFunctionDeclaration() || sp.node.params.length !== 1) continue;
    const code = JSON.stringify(sp.node.body, (k, v) => (["loc", "start", "end", "extra"].includes(k) ? undefined : v));
    if (/"value":2654435769/.test(code) && /"value":608135816/.test(code) && /"value":1779033703/.test(code)) add(programPath.scope.getBinding(sp.node.id.name));
  }
  // statement that defines each candidate
  for (const c of cands) {
    const bp = c.binding.path;
    c.stmt = bp.isFunctionDeclaration() ? bp : bp.isVariableDeclarator() ? bp.parentPath : null;
    c.writes = c.binding.constantViolations.map((cv) => (cv.parentPath.isExpressionStatement() ? cv.parentPath : null));
  }
  let live = cands.filter((c) => c.stmt && c.writes.every(Boolean) && c.stmt.parentPath.isProgram());
  for (let changed = true; changed; ) {
    changed = false;
    const holders = live.flatMap((c) => [c.stmt, ...c.writes]);
    for (const c of live) {
      const ok = c.binding.referencePaths.every((r) => holders.some((hp) => r.isDescendant(hp)));
      if (!ok) {
        live = live.filter((x) => x !== c);
        changed = true;
        break;
      }
    }
  }
  for (const c of live) {
    for (const w of c.writes) if (!w.removed) w.remove();
    if (c.stmt.isVariableDeclaration() && c.stmt.node.declarations.length > 1) c.binding.path.remove();
    else if (!c.stmt.removed) c.stmt.remove();
  }
  return live.length;
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

/** `a, b, c;` -> `a; b; c;` in case bodies and jump blocks (exact), so state
 *  updates that minify merged with user expressions separate out */
function normalizeMachine(m) {
  const isUp = (a) => t.isAssignmentExpression(a) && t.isMemberExpression(a.left, { computed: true }) && t.isIdentifier(a.left.object, { name: m.S });
  const splitSeq = (list) => {
    for (let i = 0; i < list.length; i++) {
      const st = list[i];
      if (t.isExpressionStatement(st) && t.isSequenceExpression(st.expression) && !st.expression.expressions.every(isUp)) {
        const parts = st.expression.expressions.map((x) => t.expressionStatement(x));
        list.splice(i, 1, ...parts);
        i += parts.length - 1;
        continue;
      }
      if (t.isIfStatement(st)) {
        if (t.isBlockStatement(st.consequent)) splitSeq(st.consequent.body);
        if (st.alternate && t.isBlockStatement(st.alternate)) splitSeq(st.alternate.body);
      }
    }
  };
  for (const c of m.switchNode.cases) splitSeq(c.consequent);
}

function reverseOneRound(ast, ctx) {
  roundId++;
  let programPath = crawl(ast);
  let helpers = findHelpers(programPath);
  if (!helpers.sum) return 0;
  // normalise every machine, then re-crawl so all paths/bindings are fresh
  traverse(ast, {
    FunctionDeclaration(p) {
      const m = machineOf(p, helpers);
      if (m) normalizeMachine(m);
    },
  });
  cycleCheck(ast.program, "normalize");
  programPath = crawl(ast);
  helpers = findHelpers(programPath);

  const machines = [];
  traverse(ast, {
    FunctionDeclaration(p) {
      const m = machineOf(p, helpers);
      if (m) machines.push(m);
    },
  });
  if (process.env.CFFDBG) console.error("round: helpers", Object.entries(helpers).filter(([, v]) => v).map(([k]) => k).join(","), "machines", machines.map((x) => x.name).join(","));
  // Undo every machine that neither contains nor sits inside another one
  // this round (each rewrite only touches its own function and the list
  // around its start call); nested ones wait for the next round's crawl.
  const nodesOf = new Set(machines.filter((m) => !m.fnPath.node.__cffSkip).map((m) => m.fnPath.node));
  const independent = machines.filter((m) => !m.fnPath.findParent((p) => nodesOf.has(p.node)));
  let done = 0;
  for (const m of independent) {
    if (m.fnPath.removed) continue;
    try {
      reverseMachine(m, helpers, programPath);
      done++;
    } catch (e) {
      if (!(e instanceof Bail)) throw e;
      const reason = e.message === "__skip" ? m.fnPath.node.__cffReason : e.message;
      ctx.errors.push(`controlFlowFlattening: machine ${m.name} left in place (${reason})`);
      m.fnPath.node.__cffSkip = true;
      m.fnPath.node.__cffReason = reason;
    }
  }
  return done;
}

/** names in use, collected once per round and grown as fresh names are minted */
let usedNamesCache = null;
function sharedUsedNames(programPath) {
  if (usedNamesCache && usedNamesCache.root === programPath.node && usedNamesCache.round === roundId) return usedNamesCache.set;
  const set = new Set();
  traverse(programPath.node, {
    noScope: true,
    Identifier(p) {
      set.add(p.node.name);
    },
  });
  usedNamesCache = { root: programPath.node, round: roundId, set };
  return set;
}
let roundId = 0;

function reverseMachine(m, helpers, programPath) {
  if (m.fnPath.node.__cffSkip) throw new Bail("__skip");
  const fnPath = m.fnPath;
  const statesBinding = fnPath.scope.getBinding(m.S);
  const scopeBinding = fnPath.scope.getBinding(m.scopeName);
  const isStates = (idNode, path) => path.scope.getBinding(idNode.name) === statesBinding;
  if (statesBinding.constantViolations.length) bail("states reassigned");

  /* ---- vectors */
  const evalVector = (arr, atPath) => {
    if (!t.isArrayExpression(arr)) bail("non-array state vector");
    const out = [];
    for (const e of arr.elements) {
      const v = numValue(e);
      if (v !== null) {
        out.push(v);
        continue;
      }
      if (
        t.isSpreadElement(e) &&
        t.isCallExpression(e.argument) &&
        t.isIdentifier(e.argument.callee) &&
        helpers.slice &&
        atPath.scope.getBinding(e.argument.callee.name) === helpers.slice &&
        e.argument.arguments.length === 2
      ) {
        const a = numValue(e.argument.arguments[0]);
        const b = numValue(e.argument.arguments[1]);
        if (a === null || b === null) bail("slice bounds");
        out.push(...helpers.sequence.values.slice(a, b));
        continue;
      }
      bail("unknown vector element");
    }
    return out;
  };

  /* ---- entries: start call(s) and function wrappers */
  const mainBinding = fnPath.parentPath.scope.getBinding(m.name);
  // (a declaration that shares a param's name is listed as a write to it)
  if (!mainBinding || mainBinding.constantViolations.some((cv) => cv.node !== fnPath.node)) bail("main binding");
  const entries = [];
  for (const rp of mainBinding.referencePaths) {
    const call = rp.parentPath;
    if (!call.isCallExpression() || rp.key !== "callee") bail("main referenced outside a call");
    const V = evalVector(call.node.arguments[0], call);
    // wrapper: function (...r) { return MAIN(V, {scopes}, runtime, r) }
    const ret = call.parentPath;
    const wrapperFn = ret.isReturnStatement() ? ret.parentPath.parentPath : null;
    if (
      wrapperFn &&
      wrapperFn.isFunctionExpression() &&
      wrapperFn.node.params.length === 1 &&
      t.isRestElement(wrapperFn.node.params[0]) &&
      wrapperFn.node.body.body.length === 1 &&
      call.node.arguments.length >= 2 &&
      t.isObjectExpression(call.node.arguments[1])
    ) {
      entries.push({ kind: "fn", V, call, wrapperFn, scopeObj: call.node.arguments[1], restName: wrapperFn.node.params[0].argument.name });
      continue;
    }
    if (call.node.arguments.length !== 1) bail("start call with extra arguments");
    entries.push({ kind: "start", V, call });
  }
  const starts = entries.filter((e) => e.kind === "start");
  if (starts.length !== 1) bail(`expected one start call, found ${starts.length}`);

  cycleCheck(programPath.node, "entries");
  /* ---- fold & simulate */
  const ev = makeEval(m, () => true);
  const cases = m.switchNode.cases;
  const casePaths = fnPath.get("body.body.0.body").isBlockStatement()
    ? null
    : null;
  void casePaths;
  const sum = (V) => V.reduce((a, b) => a + b, 0);

  // case consequents as paths (for binding-aware folding)
  let switchPath = fnPath.get("body.body.0.body");
  if (switchPath.isBlockStatement()) switchPath = switchPath.get("body.0");
  if (switchPath.isLabeledStatement()) switchPath = switchPath.get("body");
  const casePathList = switchPath.get("cases");

  const pickCase = (V) => {
    const target = sum(V);
    for (let i = 0; i < cases.length; i++) {
      const c = cases[i];
      if (c.test === null) bail("default case");
      const v = ev(c.test, V);
      if (v === undefined) bail("case test not evaluable");
      if (v === target) {
        let j = i;
        while (j < cases.length && cases[j].consequent.length === 0) j++;
        if (j >= cases.length) bail("fell off switch");
        return j;
      }
    }
    return -1; // no case: loop would spin forever — treat as error
  };

  const isStateUpdate = (expr) => {
    const parts = t.isSequenceExpression(expr) ? expr.expressions : [expr];
    return (
      parts.length > 0 &&
      parts.every(
        (a) =>
          t.isAssignmentExpression(a) &&
          (a.operator === "+=" || a.operator === "=") &&
          t.isMemberExpression(a.left, { computed: true }) &&
          t.isIdentifier(a.left.object, { name: m.S }),
      )
    );
  };
  const applyUpdate = (expr, V) => {
    const W = V.slice();
    const parts = t.isSequenceExpression(expr) ? expr.expressions : [expr];
    for (const a of parts) {
      const k = ev(a.left.property, W);
      const r = ev(a.right, W);
      if (!Number.isInteger(k) || r === undefined || typeof r !== "number") bail("state update not evaluable");
      W[k] = a.operator === "+=" ? W[k] + r : r;
    }
    return W;
  };
  const isBreak = (s) => t.isBreakStatement(s) && (!s.label || s.label.name === m.label);
  /** a jump body: [updates…, break] (block or single) */
  const jumpOf = (s) => {
    const list = (t.isBlockStatement(s) ? s.body : [s]).filter((x) => !t.isEmptyStatement(x));
    if (list.length < 1 || !isBreak(list[list.length - 1])) return null;
    const ups = list.slice(0, -1);
    if (!ups.every((u) => t.isExpressionStatement(u) && isStateUpdate(u.expression))) return null;
    return ups.map((u) => u.expression);
  };

  const nodes = new Map(); // key -> {V, caseIndex, stmts, exit}
  const keyOf = (V) => V.join(",");
  const consumerOf = new Map(); // caseIndex -> key (each block has one vector)

  function explore(V0) {
    const stack = [V0];
    while (stack.length) {
      const V = stack.pop();
      const key = keyOf(V);
      if (nodes.has(key)) continue;
      if (sum(V) === m.END) {
        nodes.set(key, { V, end: true });
        continue;
      }
      const ci = pickCase(V);
      if (ci < 0) bail("no case matches a reachable state");
      if (consumerOf.has(ci) && consumerOf.get(ci) !== key) bail("block reached with two state vectors");
      consumerOf.set(ci, key);
      const node = { V, caseIndex: ci };
      nodes.set(key, node);
      const exit = execList(cases[ci].consequent, 0, V, node);
      node.exit = exit;
      for (const nx of successors(exit)) stack.push(nx);
    }
  }
  function successors(exit) {
    if (!exit) return [];
    if (exit.type === "goto") return [exit.V];
    if (exit.type === "branch") return [...successors(exit.then), ...successors(exit.else)];
    return [];
  }
  // execute statements of a block from index i with vector V
  function execList(list, i, V, node) {
    node.userIdx = node.userIdx || [];
    for (; i < list.length; i++) {
      const s = list[i];
      if (t.isEmptyStatement(s)) continue;
      if (t.isExpressionStatement(s) && isStateUpdate(s.expression)) {
        V = applyUpdate(s.expression, V);
        continue;
      }
      if (isBreak(s)) return { type: "goto", V };
      // return / throw leave the function (minify drops the dead jump after them)
      if (t.isReturnStatement(s) || t.isThrowStatement(s)) {
        node.userIdx.push(i);
        return { type: "return" };
      }
      if (t.isIfStatement(s)) {
        const thenJ = jumpOf(s.consequent);
        const elseJ = s.alternate ? jumpOf(s.alternate) : null;
        if (thenJ && (!s.alternate || elseJ)) {
          const go = (ups, W) => {
            for (const u of ups) W = applyUpdate(u, W);
            return { type: "goto", V: W };
          };
          const c = ev(s.test, V);
          if (c !== undefined) {
            // constant predicate (fake jump) — take the branch it takes
            if (c) return go(thenJ, V);
            if (s.alternate) return go(elseJ, V);
            continue;
          }
          // real branch on user data
          node.branchIdx = i;
          const thenExit = go(thenJ, V);
          const elseExit = s.alternate ? go(elseJ, V) : execList(list, i + 1, V, { userIdx: [] });
          if (!s.alternate) {
            // statements after the if must be pure jump code
            for (let j = i + 1; j < list.length; j++) {
              const x = list[j];
              const pure = (t.isExpressionStatement(x) && isStateUpdate(x.expression)) || isBreak(x) ||
                (t.isIfStatement(x) && jumpOf(x.consequent) && ev(x.test, V) !== undefined);
              if (!pure) bail("user code after a branch");
              if (isBreak(x)) break;
            }
          }
          return { type: "branch", test: s.test, testIdx: i, then: thenExit, else: elseExit };
        }
      }
      node.userIdx.push(i);
    }
    bail("block without terminator" + (process.env.CFFDBG ? ": " + list.map((x) => x.type + (t.isIfStatement(x) ? "[" + generate(x).code.slice(0, 160).replace(/\s+/g, " ") + "]" : "")).join(", ") : ""));
  }

  for (const e of entries) explore(e.V);
  cycleCheck(programPath.node, "explore");

  /* ---- fold states[k] in the user statements of live blocks */
  const decodeXor = (callPath) => {
    const c = callPath.node;
    if (!helpers.xor || !t.isIdentifier(c.callee) || callPath.scope.getBinding(c.callee.name) !== helpers.xor) return;
    if (c.arguments.length !== 3) return;
    const [k, s, l] = c.arguments.map(numValue);
    if (k === null || s === null || l === null) return;
    callPath.replaceWith(t.stringLiteral(xorDecode(helpers.strings.value, k, s, l)));
  };
  const folded = new WeakSet();
  for (const node of nodes.values()) {
    if (node.end) continue;
    const cp = casePathList[node.caseIndex];
    const stmtPaths = cp.get("consequent");
    const idxs = [...(node.userIdx || [])];
    if (node.branchIdx !== undefined) idxs.push(node.branchIdx);
    for (const i of idxs) {
      const sp = stmtPaths[i];
      const foldIn = (p) => {
        p.traverse({
          "MemberExpression|BinaryExpression|UnaryExpression|LogicalExpression": {
            exit(q) {
              if (q.getFunctionParent() !== fnPath) return; // other functions have their own states
              // fold where a state ref (or an already-folded literal) is involved
              if (folded.has(q.node)) return; // already a folded literal
              let involved = false;
              if (!involved) {
                if (t.isMemberExpression(q.node) && t.isIdentifier(q.node.object, { name: m.S }) && isStates(q.node.object, q)) involved = true;
                for (const k of ["left", "right", "argument"]) if (q.node[k] && folded.has(q.node[k])) involved = true;
              }
              if (!involved) return;
              const v = ev(q.node, node.V);
              if (v === undefined) return;
              const lit = literalOf(v);
              if (lit) {
                folded.add(lit);
                if (t.isUnaryExpression(lit)) folded.add(lit.argument);
                q.replaceWith(lit);
              }
            },
          },
          CallExpression: { exit: decodeXor },
        });
      };
      if (sp.isIfStatement() && i === node.branchIdx) foldIn(sp.get("test"));
      else foldIn(sp);
    }
    // any states reference left in user code -> unsafe
    for (const i of idxs) {
      const scan = i === node.branchIdx ? stmtPaths[i].get("test") : stmtPaths[i];
      const dbg = () => (process.env.CFFDBG ? ": " + generate(stmtPaths[i].node).code.slice(0, 400) : "");
      if (scan.isMemberExpression() && t.isIdentifier(scan.node.object, { name: m.S })) bail("state value used at runtime" + dbg());
      scan.traverse({
        Identifier(r) {
          // real references only (an object key named like the states param is not one)
          if (r.node.name === m.S && r.isReferencedIdentifier() && isStates(r.node, r) && r.getFunctionParent() === fnPath)
            bail("state value used at runtime" + dbg());
        },
      });
    }
  }

  cycleCheck(programPath.node, "fold");
  /* ---- scope objects -> variables (rewrite live statements in place) */
  const scopeProps = new Map(); // "P|name" -> identifier name
  const usedNames = sharedUsedNames(programPath);
  const varName = (P, name) => {
    const k = P + "|" + name;
    if (!scopeProps.has(k)) {
      let n = t.isValidIdentifier(name) ? name : "v";
      if (usedNames.has(n)) {
        let i = 2;
        while (usedNames.has(`${n}_${i}`)) i++;
        n = `${n}_${i}`;
      }
      usedNames.add(n);
      scopeProps.set(k, n);
    }
    return scopeProps.get(k);
  };
  const isScopeRef = (node, path) => t.isIdentifier(node, { name: m.scopeName }) && path.scope.getBinding(m.scopeName) === scopeBinding;
  const scopeInits = new Set(); // `scope["P"] = {}` statements (block scopes) — dropped
  const declaredBy = new Map(); // var name -> P
  for (const node of nodes.values()) {
    if (node.end) continue;
    const stmtPaths = casePathList[node.caseIndex].get("consequent");
    const idxs = [...(node.userIdx || [])];
    if (node.branchIdx !== undefined) idxs.push(node.branchIdx);
    for (const i of idxs) {
      const sp = stmtPaths[i];
      if (
        sp.isExpressionStatement() &&
        t.isAssignmentExpression(sp.node.expression, { operator: "=" }) &&
        t.isMemberExpression(sp.node.expression.left) &&
        isScopeRef(sp.node.expression.left.object, sp) &&
        t.isObjectExpression(sp.node.expression.right) &&
        sp.node.expression.right.properties.length === 0
      ) {
        scopeInits.add(sp.node);
        continue;
      }
      const target = sp.isIfStatement() && i === node.branchIdx ? sp.get("test") : sp;
      const rewrite = (q) => {
        const o = q.node.object;
        if (!t.isMemberExpression(o) || !isScopeRef(o.object, q)) return;
        const P = memberKey(o);
        const name = memberKey(q.node);
        if (P === null || name === null) bail("dynamic scope access");
        const v = varName(P, name);
        declaredBy.set(v, P);
        q.replaceWith(t.identifier(v));
      };
      if (target.isMemberExpression()) rewrite(target);
      if (!target.removed && target.node) target.traverse({ MemberExpression: { exit: rewrite } });
    }
  }

  cycleCheck(programPath.node, "scope-rewrite");
  /* ---- post-dominators over the block DAG, then structure */
  const EXIT = "__exit";
  const succKeys = (key) => {
    const n = nodes.get(key);
    if (n.end) return [EXIT];
    const out = [];
    const walk = (x) => {
      if (x.type === "goto") out.push(keyOf(x.V));
      else if (x.type === "branch") {
        walk(x.then);
        walk(x.else);
      } else out.push(EXIT);
    };
    walk(n.exit);
    return out;
  };
  const order = [];
  const mark = new Map();
  const visit = (k) => {
    if (k === EXIT) return;
    if (mark.get(k) === 1) bail("cycle in block graph");
    if (mark.get(k) === 2) return;
    mark.set(k, 1);
    for (const s2 of succKeys(k)) visit(s2);
    mark.set(k, 2);
    order.push(k);
  };
  for (const e of entries) visit(keyOf(e.V));
  const pdom = new Map([[EXIT, new Set([EXIT])]]);
  for (const k of order) {
    let acc = null;
    for (const s2 of succKeys(k)) {
      const ps = pdom.get(s2);
      acc = acc === null ? new Set(ps) : new Set([...acc].filter((x) => ps.has(x)));
    }
    acc.add(k);
    pdom.set(k, acc);
  }
  const ipdom = (k) => {
    let best = EXIT;
    let size = 0;
    for (const c of pdom.get(k)) {
      if (c === k) continue;
      const sz = pdom.get(c).size;
      if (sz > size) {
        size = sz;
        best = c;
      }
    }
    return best;
  };
  const userStmtsOf = (n) => {
    const list = cases[n.caseIndex].consequent;
    return (n.userIdx || []).map((i) => list[i]).filter((st) => !scopeInits.has(st));
  };
  let emitted;
  const builtIfs = new WeakSet(); // if/else rebuilt from branches (may hold wrappers)
  function emit(key, stop) {
    const out = [];
    let cur = key;
    while (cur !== EXIT && cur !== stop) {
      if (emitted.has(cur)) bail("block would be emitted twice");
      emitted.add(cur);
      const n = nodes.get(cur);
      if (n.end) break;
      out.push(...userStmtsOf(n));
      const x = n.exit;
      if (x.type === "return") break;
      if (x.type === "goto") {
        cur = keyOf(x.V);
        continue;
      }
      const merge = ipdom(cur);
      const thenB = emitBranch(x.then, merge);
      const elseB = emitBranch(x.else, merge);
      const test = cases[n.caseIndex].consequent[n.branchIdx].test;
      let made;
      if (thenB.length === 0 && elseB.length === 0) made = t.expressionStatement(test);
      else if (thenB.length === 0) made = t.ifStatement(t.unaryExpression("!", test), t.blockStatement(elseB));
      else made = t.ifStatement(test, t.blockStatement(thenB), elseB.length ? t.blockStatement(elseB) : null);
      if (t.isIfStatement(made)) builtIfs.add(made);
      out.push(made);
      cur = merge;
    }
    return out;
  }
  function emitBranch(x, merge) {
    if (x.type === "goto") return emit(keyOf(x.V), merge);
    if (x.type === "branch") bail("nested branch exit");
    return [];
  }

  /* ---- which scope objects each entry owns */
  const keyOfProp = (p) =>
    t.isObjectProperty(p) ? (p.computed ? propKey(p.key) : t.isIdentifier(p.key) ? p.key.name : propKey(p.key)) : null;
  const ownProps = new Map();
  for (const e of entries) {
    const own = new Set();
    const obj = e.kind === "start" ? m.defaultScope : e.scopeObj;
    for (const p of obj.properties) {
      const k = keyOfProp(p);
      if (k === null) bail("scope object key");
      if (t.isObjectExpression(p.value) && p.value.properties.length === 0) own.add(k);
      else if (!(e.kind === "fn" && t.isMemberExpression(p.value) && t.isIdentifier(p.value.object, { name: m.scopeName }) && memberKey(p.value) === k))
        bail("scope object value");
    }
    ownProps.set(e, own);
  }

  /* ---- emit every entry */
  const bodyOf = new Map();
  for (const e of entries) {
    emitted = new Set();
    bodyOf.set(e, emit(keyOf(e.V), null));
  }
  // block-scope objects belong to the entry whose blocks initialise them
  for (const e of entries)
    for (const node of nodes.values()) {
      if (node.end) continue;
      for (const i of node.userIdx || []) {
        const st = cases[node.caseIndex].consequent[i];
        if (scopeInits.has(st)) {
          // owner: the entry that emitted this block
          emitted = null;
        }
      }
    }
  const blockScopeOwner = new Map();
  for (const e of entries) {
    emitted = new Set();
    const reach = [];
    const stack = [keyOf(e.V)];
    while (stack.length) {
      const k = stack.pop();
      if (k === EXIT || reach.includes(k)) continue;
      reach.push(k);
      stack.push(...succKeys(k));
    }
    for (const k of reach) {
      const n = nodes.get(k);
      if (n.end) continue;
      for (const i of n.userIdx || []) {
        const st = cases[n.caseIndex].consequent[i];
        if (scopeInits.has(st)) {
          const P = memberKey(st.expression.left);
          if (blockScopeOwner.has(P) && blockScopeOwner.get(P) !== e) bail("block scope shared by two functions");
          blockScopeOwner.set(P, e);
        }
      }
    }
  }
  const ownerOf = (P) => {
    for (const e of entries) if (ownProps.get(e).has(P)) return e;
    return blockScopeOwner.get(P) || null;
  };
  for (const [, P] of declaredBy) if (!ownerOf(P)) bail(`scope ${P} has no owner`);

  // runtime / arg variables: only allowed where the template puts them
  const runtimeBinding = m.runtimeName ? fnPath.scope.getBinding(m.runtimeName) : null;
  if (runtimeBinding)
    for (const r of runtimeBinding.referencePaths)
      if (!entries.some((e) => e.kind === "fn" && r.isDescendant(e.call))) bail("runtime variable used");

  /* ---- assemble: wrapper statements become function declarations */
  const wrapperStmtOf = new Map(); // statement node -> entry
  for (const e of entries) {
    if (e.kind !== "fn") continue;
    const assign = e.wrapperFn.parentPath;
    if (!(assign.isAssignmentExpression({ operator: "=" }) && t.isIdentifier(assign.node.left) && assign.parentPath.isExpressionStatement()))
      bail("function wrapper not assigned to a variable");
    e.fnName = assign.node.left.name;
    wrapperStmtOf.set(assign.parentPath.node, e);
  }
  const finished = new Map();
  const placed = new Set();
  const unpackRefs = new Set(); // `arg` nodes consumed by parameter unpacks
  function finish(e) {
    if (finished.has(e)) return finished.get(e);
    finished.set(e, null); // cycle guard
    const swap = (list) =>
      list.map((st) => {
        if (builtIfs.has(st)) {
          st.consequent.body = swap(st.consequent.body);
          if (st.alternate) st.alternate.body = swap(st.alternate.body);
          return st;
        }
        const w = wrapperStmtOf.get(st);
        if (!w) return st;
        placed.add(w);
        const f = finish(w);
        return t.functionDeclaration(t.identifier(w.fnName), f.params, t.blockStatement(f.body));
      });
    let stmts = swap(bodyOf.get(e));
    let params = [];
    if (e.kind === "fn") {
      // the parameter unpack `[a, b] = arg` — possibly after hoisted function
      // declarations / bare vars, which execute nothing
      let at = 0;
      while (
        at < stmts.length &&
        (t.isFunctionDeclaration(stmts[at]) || (t.isVariableDeclaration(stmts[at]) && stmts[at].declarations.every((d) => !d.init)))
      )
        at++;
      const first = stmts[at];
      if (
        first &&
        t.isExpressionStatement(first) &&
        t.isAssignmentExpression(first.expression, { operator: "=" }) &&
        t.isArrayPattern(first.expression.left) &&
        t.isIdentifier(first.expression.right) &&
        first.expression.right.name === m.argName
      ) {
        params = first.expression.left.elements;
        if (params.some((x) => x === null)) bail("parameter hole");
        unpackRefs.add(first.expression.right);
        stmts = [...stmts.slice(0, at), ...stmts.slice(at + 1)];
      }
      const last = stmts[stmts.length - 1];
      if (isEmptyReturn(last)) stmts = stmts.slice(0, -1);
    }
    const paramNames = new Set(params.flatMap((p) => Object.keys(t.getBindingIdentifiers(p))));
    const fnDeclNames = new Set(stmts.filter((x) => t.isFunctionDeclaration(x)).map((x) => x.id.name));
    const vars = [...declaredBy.entries()]
      .filter(([v, P]) => ownerOf(P) === e && !paramNames.has(v) && !fnDeclNames.has(v))
      .map(([v]) => t.variableDeclaration("var", [t.variableDeclarator(t.identifier(v))]));
    const res = { params, body: [...vars, ...stmts] };
    finished.set(e, res);
    return res;
  }
  for (const e of entries) finish(e);
  // every wrapper must have been placed inside some emitted body
  // the argument array may only feed parameter unpacks (binding-checked: the
  // renamer reuses short names, so a same-named identifier elsewhere is fine)
  if (m.argName) {
    const argBinding = fnPath.scope.getBinding(m.argName);
    if (argBinding && fnPath.scope.getOwnBinding(m.argName) === argBinding)
      for (const r of argBinding.referencePaths)
        if (!unpackRefs.has(r.node)) bail("argument array used beyond parameters");
  }
  for (const e of entries)
    if (e.kind === "fn" && !placed.has(e)) {
      if (process.env.CFFDBG) {
        const st = [...wrapperStmtOf.entries()].find(([, x]) => x === e)[0];
        const owner = [...nodes.values()].find((n) => !n.end && cases[n.caseIndex].consequent.includes(st));
        const caseOf = cases.findIndex((c) => c.consequent.includes(st));
        console.error("unplaced wrapper", e.fnName, "case", caseOf, "live node?", !!owner, owner ? "userIdx " + JSON.stringify(owner.userIdx) + " idx " + cases[owner.caseIndex].consequent.indexOf(st) : "");
      }
      bail("function wrapper not in a live block");
    }

  cycleCheck(programPath.node, "finish");
  /* ---- replace machine + start statements */
  const start = starts[0];
  const startBody = finished.get(start).body;
  const callStmt = start.call.parentPath;
  const container = fnPath.parentPath;
  const list = container.node.body;
  if (callStmt.isExpressionStatement()) {
    // program-level: `MAIN(V);` — the program's last expression became `return expr`
    const fixed = startBody.map((st) => (t.isReturnStatement(st) && st.argument ? t.expressionStatement(st.argument) : st));
    list.splice(list.indexOf(callStmt.node), 1, ...fixed);
  } else if (
    callStmt.isVariableDeclarator() ||
    (callStmt.isAssignmentExpression({ operator: "=" }) && t.isIdentifier(callStmt.node.left) && callStmt.parentPath.isExpressionStatement())
  ) {
    // function-level: var didReturn; var result = MAIN(V); if (didReturn) { return result; }
    // (Moved Declarations may have turned the vars into `x = …` assignments)
    const declStmt = callStmt.parentPath.node;
    const i = list.indexOf(declStmt);
    const resultName = callStmt.isVariableDeclarator() ? callStmt.node.id.name : callStmt.node.left.name;
    const prev = list[i - 1];
    const next = list[i + 1];
    // `var didReturn;` — or `didReturn = undefined;` after Moved Declarations
    let didReturnName = null;
    const isUndef = (x) => !x || t.isIdentifier(x, { name: "undefined" }) || (t.isUnaryExpression(x, { operator: "void" }) && t.isNumericLiteral(x.argument));
    if (t.isVariableDeclaration(prev) && prev.declarations.length === 1 && t.isIdentifier(prev.declarations[0].id) && isUndef(prev.declarations[0].init))
      didReturnName = prev.declarations[0].id.name;
    else if (t.isExpressionStatement(prev) && t.isAssignmentExpression(prev.expression, { operator: "=" }) && t.isIdentifier(prev.expression.left) &&
      t.isIdentifier(prev.expression.right, { name: "undefined" })) didReturnName = prev.expression.left.name;
    const only = (st) => (t.isBlockStatement(st) ? (st.body.length === 1 ? st.body[0] : null) : st);
    const ret = next && t.isIfStatement(next) ? only(next.consequent) : null;
    const alt = next && t.isIfStatement(next) && next.alternate ? only(next.alternate) : null;
    if (
      !didReturnName ||
      !t.isIdentifier(next.test, { name: didReturnName }) ||
      !t.isReturnStatement(ret) ||
      !t.isIdentifier(ret.argument, { name: resultName }) ||
      (next.alternate && !(t.isReturnStatement(alt) && (!alt.argument || t.isIdentifier(alt.argument, { name: "undefined" }))))
    )
      bail("function-level start shape" + (process.env.CFFDBG ? ": " + [prev, declStmt, next].map((x) => (x ? generate(x).code : "<none>")).join(" ⏎ ").slice(0, 600) : ""));
    // the didReturn / result variables must not be used anywhere else
    for (const nm of [didReturnName, resultName]) {
      const b = fnPath.parentPath.scope.getBinding(nm);
      if (!b) continue;
      const uses = [...b.referencePaths, ...b.constantViolations].filter(
        (u) => !(u.findParent((x) => x.node === prev || x.node === next || x.node === declStmt) || u.node === prev || u.node === declStmt),
      );
      const inReturns = uses.every((u) => u.findParent((x) => x.isReturnStatement()) && u.isDescendant(fnPath));
      if (!inReturns) bail("didReturn/result used elsewhere");
    }
    for (const st of startBody)
      traverse(t.file(t.program([st])), {
        noScope: true,
        Function(fp) {
          fp.skip();
        },
        ReturnStatement(rp) {
          const a = rp.node.argument;
          if (
            t.isSequenceExpression(a) &&
            a.expressions.length === 2 &&
            t.isAssignmentExpression(a.expressions[0], { operator: "=" }) &&
            t.isIdentifier(a.expressions[0].left, { name: didReturnName }) &&
            t.isBooleanLiteral(a.expressions[0].right, { value: true })
          )
            rp.node.argument = a.expressions[1];
        },
      });
    list.splice(i - 1, 3, ...startBody);
  } else bail("start call shape");
  list.splice(list.indexOf(fnPath.node), 1);
  cycleCheck(programPath.node, "replace");

  // simplify `(1, f)(…)` left by "preserve this" calls
  traverse(container.node, {
    noScope: true,
    CallExpression(p) {
      const c = p.node.callee;
      if (t.isSequenceExpression(c) && c.expressions.length === 2 && t.isNumericLiteral(c.expressions[0]) && t.isIdentifier(c.expressions[1]))
        p.node.callee = c.expressions[1];
    },
  });
}
export { findHelpers as _findHelpers, machineOf as _machineOf, crawl as _crawl };
