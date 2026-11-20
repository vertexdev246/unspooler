/**
 * JSDefender control-flow flattening -> structured code.
 *
 *   var S = INIT;
 *   [{ let a, b; ]  while (S < END) [{] switch (S) {
 *     case K: S = NEXT;              // NEXT: a number, or  test ? A : B
 *             { ...body... }         // the case's original statements
 *             break;                 // (or the body ends in return / throw)
 *     ...
 *   } [}] [}]
 *
 * Execution starts at INIT; a state >= END leaves the machine. Fake cases
 * (injectFakeCode) are simply unreachable. The state graph is turned back
 * into loops / if-else / break / continue. Refused (left as is): the state
 * variable used outside the dispatch, a break/continue aimed at the dispatcher
 * from inside a body, a jump to a state with no case (an infinite loop in the
 * original), case-level lexical declarations, irreducible shapes.
 */
import { createRequire } from "module";
const require = createRequire(import.meta.url);
const traverse = require("@babel/traverse").default;
const t = require("@babel/types");

class Refuse extends Error {}
const EXIT = "exit";
const NONE = Symbol("no join"); // a stop that is never reached: emit until a jump / return

const numOf = (n) => (t.isNumericLiteral(n) ? n.value : t.isUnaryExpression(n, { operator: "-" }) && t.isNumericLiteral(n.argument) ? -n.argument.value : null);

/** parse one machine; returns {S, init, end, cases: Map(state -> {body, next}), locals, whilePath} or null */
function readMachine(declStmt, nextStmt) {
  if (!t.isVariableDeclaration(declStmt, { kind: "var" }) || declStmt.declarations.length !== 1) return null;
  const d = declStmt.declarations[0];
  if (!t.isIdentifier(d.id) || numOf(d.init) === null) return null;
  const S = d.id.name, init = numOf(d.init);
  let locals = null, loop = nextStmt;
  if (t.isBlockStatement(nextStmt)) {
    const b = nextStmt.body;
    if (b.length < 2 || !t.isVariableDeclaration(b[0]) || b[0].kind === "var" || !(t.isWhileStatement(b[1]) || t.isLabeledStatement(b[1]))) return null;
    locals = b[0];
    loop = b[1];
    var rest = b.slice(2); // statements after the machine, still inside the locals' block
  }
  // `L: while (…)` — a `break L` inside a case leaves the machine; kept as `L: { … }`
  let label = null;
  if (t.isLabeledStatement(loop)) { label = loop.label.name; loop = loop.body; }
  if (!t.isWhileStatement(loop) || !t.isBinaryExpression(loop.test, { operator: "<" }) || !t.isIdentifier(loop.test.left, { name: S }) || numOf(loop.test.right) === null) return null;
  const end = numOf(loop.test.right);
  let sw = loop.body;
  if (t.isBlockStatement(sw)) { if (sw.body.length !== 1) return null; sw = sw.body[0]; }
  if (!t.isSwitchStatement(sw) || !t.isIdentifier(sw.discriminant, { name: S })) return null;
  const isStateAssign = (st) => t.isExpressionStatement(st) && t.isAssignmentExpression(st.expression, { operator: "=" }) && t.isIdentifier(st.expression.left, { name: S });
  const parseNext = (r) => {
    if (numOf(r) !== null) return { to: numOf(r) };
    if (t.isConditionalExpression(r) && numOf(r.consequent) !== null && numOf(r.alternate) !== null) return { test: r.test, a: numOf(r.consequent), b: numOf(r.alternate) };
    return null;
  };
  const cases = new Map();
  for (const c of sw.cases) {
    const k = c.test ? numOf(c.test) : null;
    if (k === null || cases.has(k)) return null;
    const cons = c.consequent;
    if (!cons.length || !isStateAssign(cons[0])) return null;
    let next = parseNext(cons[0].expression.right);
    if (!next) return null;
    let body = cons.slice(1);
    // absorb redundant leading state assignments (JSDefender writes S twice; the last wins).
    // the dropped ones must be plain constants (no side effects to lose).
    while (body.length && isStateAssign(body[0])) {
      const t2 = parseNext(body[0].expression.right);
      if (!t2 || next.test) break; // only drop a constant assignment
      next = t2;
      body = body.slice(1);
    }
    // any further state write interleaved with effects: can't model the transfer order
    if (body.some(isStateAssign)) return null;
    const last = body[body.length - 1];
    let terminal = false;
    // the switch is the whole while body, so an (unlabelled) break, an (unlabelled)
    // continue, and a `continue <machineLabel>` all do the same thing: re-dispatch.
    const isRedispatch = (st) =>
      (t.isBreakStatement(st) && !st.label) ||
      (t.isContinueStatement(st) && (!st.label || (label && st.label.name === label)));
    if (isRedispatch(last)) body = body.slice(0, -1);
    else if (t.isReturnStatement(last) || t.isThrowStatement(last)) terminal = true;
    // a break/continue to an *enclosing* label (not the machine's own) leaves the
    // machine for good — keep it in the body and treat the case as terminal.
    else if ((t.isBreakStatement(last) || t.isContinueStatement(last)) && last.label && last.label.name !== label && !next.test) terminal = true;
    else return null;
    cases.set(k, { body, next, terminal, node: c });
  }
  return { S, init, end, cases, locals, loop, sw, label, rest: typeof rest === "undefined" ? [] : rest };
}

/** a break/continue inside `body` that would target the dispatcher switch / while */
function hasDispatcherJump(stmts) {
  let bad = false;
  const visit = (n, inLoop, inSwitch) => {
    if (!n || typeof n !== "object" || bad) return;
    if (Array.isArray(n)) return n.forEach((x) => visit(x, inLoop, inSwitch));
    if (t.isFunction(n)) return;
    if (t.isBreakStatement(n) && !n.label && !inLoop && !inSwitch) bad = true;
    if (t.isContinueStatement(n) && !n.label && !inLoop) bad = true;
    if (t.isLabeledStatement(n)) return visit(n.body, inLoop, inSwitch); // labelled jumps keep their target
    const loop = t.isLoop(n), sw = t.isSwitchStatement(n);
    for (const k of t.VISITOR_KEYS[n.type] || []) visit(n[k], inLoop || loop, inSwitch || sw);
  };
  visit(stmts, false, false);
  return bad;
}

function hasLabelledContinue(stmts, label) {
  let hit = false;
  const visit = (n) => {
    if (!n || typeof n !== "object" || hit) return;
    if (Array.isArray(n)) return n.forEach(visit);
    if (t.isFunction(n)) return;
    if (t.isContinueStatement(n) && n.label && n.label.name === label) hit = true;
    for (const k of t.VISITOR_KEYS[n.type] || []) visit(n[k]);
  };
  visit(stmts);
  return hit;
}

function structure(m) {
  // When the dispatch variable is read after the machine, each exit must carry
  // the concrete state value it left with. Represent those as distinct string
  // sinks "__exitN"; otherwise one plain EXIT sink (behaviour unchanged).
  const mkExit = (v) => (m.liveOut ? "__exit" + v : EXIT);
  const isExit = (x) => x === EXIT || (typeof x === "string" && x[0] === "_" && x.startsWith("__exit"));
  const exitValOf = (x) => (typeof x === "string" && x.startsWith("__exit") ? +x.slice(6) : null);
  const stateAssign = (v) => t.expressionStatement(t.assignmentExpression("=", t.identifier(m.S), t.numericLiteral(v)));
  const node = (k) => (k >= m.end ? mkExit(k) : m.cases.has(k) ? k : (() => { throw new Refuse("jump to a state with no case"); })());
  // reachable graph
  const succ = new Map();
  const order = [];
  const seen = new Set();
  const stack = [node(m.init)];
  while (stack.length) {
    const k = stack.pop();
    if (isExit(k) || seen.has(k)) continue;
    seen.add(k);
    order.push(k);
    const c = m.cases.get(k);
    if (hasDispatcherJump(c.body)) throw new Refuse("break/continue aimed at the dispatcher");
    if (m.label && hasLabelledContinue(c.body, m.label)) throw new Refuse("continue to the machine label");
    for (const s of c.body) if (t.isVariableDeclaration(s) && s.kind !== "var" || t.isClassDeclaration(s) || t.isFunctionDeclaration(s)) throw new Refuse("case-level declaration");
    const ss = c.terminal ? [] : c.next.test ? [node(c.next.a), node(c.next.b)] : [node(c.next.to)];
    succ.set(k, ss);
    for (const s of ss) stack.push(s);
  }
  // DFS for back edges / loop headers
  const headers = new Map(); // header -> Set(latches)
  const state = new Map();
  const dfs = (k) => {
    state.set(k, 1);
    for (const s of succ.get(k)) {
      if (isExit(s)) continue;
      if (state.get(s) === 1) { if (!headers.has(s)) headers.set(s, new Set()); headers.get(s).add(k); }
      else if (!state.has(s)) dfs(s);
    }
    state.set(k, 2);
  };
  dfs(node(m.init));
  // natural loop bodies
  const preds = new Map([...seen].map((k) => [k, []]));
  for (const [k, ss] of succ) for (const s of ss) if (!isExit(s)) preds.get(s).push(k);
  const loops = new Map();
  for (const [h, latches] of headers) {
    const body = new Set([h]);
    const work = [...latches];
    while (work.length) { const x = work.pop(); if (!body.has(x)) { body.add(x); work.push(...preds.get(x)); } }
    const exits = new Set();
    for (const x of body) for (const s of succ.get(x)) if (!body.has(s)) exits.add(s);
    if (exits.size > 1) throw new Refuse("loop with several exits");
    loops.set(h, { body, follow: exits.size ? [...exits][0] : null });
  }
  // post-dominators over a region (nodes + virtual sinks), small graphs: iterative sets
  const ipdom = (from, region, sinkOf) => {
    // reachable nodes within region from `from`
    const nodes = [];
    const vis = new Set();
    const st = [from];
    while (st.length) { const x = st.pop(); if (vis.has(x)) continue; vis.add(x); nodes.push(x); if (typeof x === "string") continue; for (const s of region.succ(x)) st.push(s); }
    const pd = new Map(nodes.map((x) => [x, typeof x === "string" ? new Set([x]) : new Set(nodes)]));
    for (let ch = true; ch;) {
      ch = false;
      for (const x of nodes) {
        if (typeof x === "string") continue;
        const ss = region.succ(x);
        let inter = null;
        for (const s of ss) { const p = pd.get(s); inter = inter ? new Set([...inter].filter((y) => p.has(y))) : new Set(p); }
        inter = inter || new Set();
        inter.add(x);
        if (inter.size !== pd.get(x).size) { pd.set(x, inter); ch = true; }
      }
    }
    // immediate: the strict post-dominator closest to `from`
    const cands = [...pd.get(from)].filter((y) => y !== from);
    return cands.find((c) => cands.every((o) => o === c || pd.get(c)?.has(o))) ?? null;
  };

  let steps = 0;
  const emit = (from, stop, ctx) => {
    const out = [];
    let k = from;
    while (k !== stop) {
      if (++steps > 20000) throw new Refuse("structuring did not converge");
      if (ctx.loop && k === ctx.loop.follow) { out.push(t.breakStatement()); return out; }
      if (ctx.loop && k === ctx.loop.header && !ctx.atHeader) { out.push(t.continueStatement()); return out; }
      if (isExit(k)) {
        const ev = exitValOf(k);
        if (ev !== null) out.push(stateAssign(ev)); // the machine's dispatch value is read afterwards
        if (ctx.loop) out.push(t.breakStatement(t.identifier(ctx.label())));
        return out;
      }
      const lp = loops.get(k);
      if (lp && !(ctx.loop && ctx.loop.header === k)) {
        const inner = { header: k, follow: lp.follow, body: lp.body };
        const bodyStmts = emit(k, null, { ...ctx, loop: inner, atHeader: true, outer: ctx });
        out.push(t.forStatement(null, null, null, t.blockStatement(bodyStmts)));
        if (lp.follow === null) return out;
        k = lp.follow;
        continue;
      }
      ctx = { ...ctx, atHeader: false };
      const c = m.cases.get(k);
      out.push(...c.body.map((s) => t.cloneNode(s, true)));
      if (c.terminal) return out;
      if (!c.next.test) { k = node(c.next.to); continue; }
      const a = node(c.next.a), b = node(c.next.b);
      // region successor function: loop control targets are sinks
      const region = { succ: (x) => (succ.get(x) || []).map((s) => (ctx.loop && (s === ctx.loop.header || s === ctx.loop.follow) ? "ctl" : s)) };
      // a jump = loop control, or leaving the machine. A bare EXIT outside a loop joins
      // at the end (no assignment); a valued "__exit" sink always jumps so each carries its own S=.
      const jumpOf = (x) => (typeof x === "string" && x.startsWith("__exit")) || !!(ctx.loop && (x === ctx.loop.header || x === ctx.loop.follow || x === EXIT));
      if (jumpOf(a) && !jumpOf(b)) { out.push(t.ifStatement(t.cloneNode(c.next.test, true), t.blockStatement(emit(a, b, ctx)))); k = b; continue; }
      if (jumpOf(b) && !jumpOf(a)) { out.push(t.ifStatement(t.unaryExpression("!", t.cloneNode(c.next.test, true)), t.blockStatement(emit(b, a, ctx)))); k = a; continue; }
      // join = immediate post-dominator; when the branches only meet at a jump (loop control /
      // leaving the machine) there is no join: each branch is emitted to its own end
      let join = ipdom(k, region);
      if (join === null || typeof join === "string") join = NONE;
      const thenS = emit(a, join, ctx), elseS = emit(b, join, ctx);
      out.push(t.ifStatement(t.cloneNode(c.next.test, true), t.blockStatement(thenS), elseS.length ? t.blockStatement(elseS) : null));
      if (join === NONE) return out;
      k = join;
    }
    return out;
  };
  let needLabel = false;
  const label = "jsd_machine";
  const top = emit(node(m.init), EXIT, { loop: null, label: () => { needLabel = true; return label; } });
  return { stmts: top, needLabel, label };
}

/**
 * Replace every recognisable machine in `ast`. Returns the number rewritten.
 */
export function unflattenJsdefender(ast) {
  let n = 0;
  traverse(ast, {
    "BlockStatement|Program": {
      exit(p) {
        const list = p.node.body;
        for (let i = 0; i + 1 < list.length; i++) {
          const m = readMachine(list[i], list[i + 1]);
          if (!m) continue;
          // the state variable must not be used anywhere else
          const b = p.scope.getBinding(m.S);
          if (!b) continue;
          const machineNodes = new Set([list[i], list[i + 1]]);
          const inside = (rp) => { for (let q = rp; q; q = q.parentPath) if (machineNodes.has(q.node)) return true; return false; };
          // writes to the dispatch var outside the machine would corrupt it — refuse.
          // reads outside are fine: the machine keeps the dispatch var live and assigns its exit value.
          if (b.constantViolations.some((cv) => !inside(cv))) continue;
          m.liveOut = b.referencePaths.some((rp) => !inside(rp));
          let res;
          try { res = structure(m); } catch (e) { if (e instanceof Refuse || e instanceof RangeError) continue; throw e; }
          let body = res.stmts;
          if (res.needLabel) body = [t.labeledStatement(t.identifier(res.label), t.blockStatement(body))];
          if (m.label) body = [t.labeledStatement(t.identifier(m.label), t.blockStatement(body))];
          // the dispatch var is read after the machine: keep it declared (now assigned at each exit)
          if (m.liveOut) body = [t.variableDeclaration("var", [t.variableDeclarator(t.identifier(m.S))]), ...body];
          const repl = m.locals ? [t.blockStatement([m.locals, ...body, ...m.rest])] : body;
          list.splice(i, 2, ...repl);
          n++;
          i += repl.length - 1;
        }
      },
    },
  });
  return n;
}


/**
 * Exact loop clean-up after restructuring:
 *  - a trailing `continue;` in a loop body is a no-op
 *  - for (;;) { if (C) break; …B } -> while (!C) { …B }
 *  - x = I; while (C) { …B; U }  -> for (x = I; C; U) { …B }   when B has no
 *    `continue` for this loop (a continue would skip U in the while form)
 */
export function tidyLoops(ast) {
  let n = 0;
  const negate = (e) => (t.isUnaryExpression(e, { operator: "!" }) ? e.argument : t.unaryExpression("!", e));
  const hasOwnContinue = (stmts) => {
    let hit = false;
    const visit = (x, inner) => {
      if (!x || typeof x !== "object" || hit) return;
      if (Array.isArray(x)) return x.forEach((y) => visit(y, inner));
      if (t.isFunction(x)) return;
      if (t.isContinueStatement(x) && (!inner || x.label)) hit = true; // labelled continues: be conservative
      for (const k of t.VISITOR_KEYS[x.type] || []) visit(x[k], inner || t.isLoop(x));
    };
    visit(stmts, false);
    return hit;
  };
  traverse(ast, {
    Loop: {
      exit(p) {
        const b = p.node.body;
        if (t.isBlockStatement(b) && b.body.length && t.isContinueStatement(b.body[b.body.length - 1]) && !b.body[b.body.length - 1].label) { b.body.pop(); n++; }
      },
    },
    ForStatement: {
      exit(p) {
        const f = p.node;
        if (f.init || f.test || f.update || !t.isBlockStatement(f.body) || !f.body.body.length) return;
        const first = f.body.body[0];
        if (!t.isIfStatement(first) || first.alternate) return;
        const c = t.isBlockStatement(first.consequent) && first.consequent.body.length === 1 ? first.consequent.body[0] : first.consequent;
        if (!t.isBreakStatement(c) || c.label) return;
        p.replaceWith(t.whileStatement(negate(first.test), t.blockStatement(f.body.body.slice(1))));
        n++;
      },
    },
    "BlockStatement|Program": {
      exit(p) {
        const list = p.node.body;
        for (let i = 0; i + 1 < list.length; i++) {
          const a = list[i], w = list[i + 1];
          if (!t.isWhileStatement(w) || !t.isBlockStatement(w.body) || w.body.body.length < 1) continue;
          if (!t.isExpressionStatement(a) || !t.isAssignmentExpression(a.expression, { operator: "=" }) || !t.isIdentifier(a.expression.left)) continue;
          const last = w.body.body[w.body.body.length - 1];
          if (!t.isExpressionStatement(last) || !(t.isUpdateExpression(last.expression) || t.isAssignmentExpression(last.expression)) ) continue;
          const tgt = t.isUpdateExpression(last.expression) ? last.expression.argument : last.expression.left;
          if (!t.isIdentifier(tgt, { name: a.expression.left.name })) continue;
          const body = w.body.body.slice(0, -1);
          if (hasOwnContinue(body)) continue;
          list.splice(i, 2, t.forStatement(a.expression, w.test, last.expression, t.blockStatement(body)));
          n++;
        }
      },
    },
  });
  return n;
}
