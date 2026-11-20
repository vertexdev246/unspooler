/**
 * Pass: js-virtualizer wrappers -> lifted JavaScript.
 *
 * Wrapper shape (src/templates/functionWrapper.template), matched through
 * scope bindings so renamed variables (the ObfuscateTranspiled pass runs
 * JS-Confuser over it) don't matter:
 *
 *   [async] function f(a, b) {
 *     const VM = new JSVM();
 *     VM.loadFromString("<base64>", "base64");
 *     VM.loadDependencies({ 47: a, 188: b, 12: console });
 *     VM.run();                 // or: await VM.runAsync();
 *     return VM.registers[167];
 *   }
 *   with  const JSVM = require("<vm path>");
 *
 * The opcode numbering comes from a companion VM file (ctx.jsvTables, filled
 * by deobfuscate() from options.companions). Without one only the stock
 * numbering is tried, and only when the build provably didn't shuffle — we
 * can't prove that from the transpiled file alone, so we refuse instead.
 */
import { decodeBlob, disassemble, JsvError } from "./jsvirt.mjs";
import { liftFunction, LiftError } from "./jsvirt-lift.mjs";

export function unJsVirtualizer(ast, ctx, { traverse, t, parse, recrawl }) {
  recrawl(ast);
  const sites = [];
  const vmCtors = new Set(); // bindings of `const JSVM = require(...)`
  traverse(ast, {
    Function(fp) {
      const fn = fp.node;
      if (!t.isBlockStatement(fn.body)) return;
      const body = fn.body.body;
      if (body.length !== 5) return;
      const [decl, load, deps, run, ret] = body;
      // const VM = new JSVM();
      if (!t.isVariableDeclaration(decl) || decl.declarations.length !== 1) return;
      const d = decl.declarations[0];
      if (!t.isIdentifier(d.id) || !t.isNewExpression(d.init) || !t.isIdentifier(d.init.callee) || d.init.arguments.length) return;
      const vmName = d.id.name;
      const ctorB = fp.scope.getBinding(d.init.callee.name);
      if (!ctorB || !ctorB.path.isVariableDeclarator()) return;
      const isReq = (req) => t.isCallExpression(req) && t.isIdentifier(req.callee, { name: "require" }) && req.arguments.length === 1 && t.isStringLiteral(req.arguments[0]);
      if (ctorB.constantViolations.length === 0) {
        if (!isReq(ctorB.path.node.init)) return;
      } else {
        // `var JSVM; … JSVM = require("…");` (JS-Confuser Moved Declarations): one assignment,
        // a top-level statement of the wrapper's own statement list, before every use of the wrapper
        if (ctorB.path.node.init || ctorB.constantViolations.length !== 1) return;
        const asg = ctorB.constantViolations[0];
        if (!asg.isAssignmentExpression({ operator: "=" }) || !isReq(asg.node.right) || !asg.parentPath.isExpressionStatement()) return;
        const stmt = asg.parentPath;
        const fnStmt = fp.isFunctionDeclaration() ? fp : fp.parentPath.isVariableDeclarator() ? fp.parentPath.parentPath : null;
        if (!fnStmt || stmt.parentPath !== fnStmt.parentPath || !Array.isArray(stmt.container)) return;
        const fnB = fp.isFunctionDeclaration() ? fp.parentPath.scope.getBinding(fp.node.id.name) : fp.parentPath.scope.getBinding(fp.parentPath.node.id.name);
        if (!fnB) return;
        const topIndex = (rp) => { let q = rp; while (q && q.parentPath !== stmt.parentPath) q = q.parentPath; return q ? q.key : -1; };
        if (!fnB.referencePaths.every((rp) => topIndex(rp) > stmt.key)) return;
      }
      const isCall = (st, prop, nargs) => {
        let e = t.isExpressionStatement(st) ? st.expression : null;
        if (t.isAwaitExpression(e)) e = e.argument;
        return t.isCallExpression(e) && t.isMemberExpression(e.callee) && t.isIdentifier(e.callee.object, { name: vmName }) &&
          (e.callee.computed ? t.isStringLiteral(e.callee.property, { value: prop }) : t.isIdentifier(e.callee.property, { name: prop })) &&
          e.arguments.length === nargs ? e : null;
      };
      const lc = isCall(load, "loadFromString", 2);
      if (!lc || !t.isStringLiteral(lc.arguments[0]) || !t.isStringLiteral(lc.arguments[1])) return;
      const dc = isCall(deps, "loadDependencies", 1);
      if (!dc || !t.isObjectExpression(dc.arguments[0])) return;
      const isAsyncRun = t.isExpressionStatement(run) && t.isAwaitExpression(run.expression);
      if (!isCall(run, isAsyncRun ? "runAsync" : "run", 0)) return;
      if (!!fn.async !== isAsyncRun) return;
      if (!t.isReturnStatement(ret) || !t.isMemberExpression(ret.argument, { computed: true })) return;
      const regs = ret.argument.object;
      if (!t.isMemberExpression(regs) || !t.isIdentifier(regs.object, { name: vmName }) || !(regs.computed ? t.isStringLiteral(regs.property, { value: "registers" }) : t.isIdentifier(regs.property, { name: "registers" }))) return;
      if (!t.isNumericLiteral(ret.argument.property)) return;
      // the VM object must not escape the wrapper
      const vb = fp.scope.getBinding(vmName);
      if (!vb || vb.referencePaths.length !== 4 || vb.constantViolations.length) return;
      // dependencies: { reg: identifier }
      const depMap = new Map();
      for (const p of dc.arguments[0].properties) {
        // `[58]: d` (computed numeric key) means the same as `58: d`
        if (!t.isObjectProperty(p) || !t.isNumericLiteral(p.key) || !t.isIdentifier(p.value)) return;
        const name = p.value.name;
        const isParam = fn.params.some((q) => (t.isIdentifier(q) && q.name === name) || (t.isAssignmentPattern(q) && t.isIdentifier(q.left, { name })) || (t.isRestElement(q) && t.isIdentifier(q.argument, { name })));
        const ob = fp.scope.getBinding(name);
        // an outer variable may be read directly when nothing ever reassigns it (the VM snapshots it on entry)
        const direct = isParam ? true : ob ? ob.constantViolations.length === 0 : !assignedGlobals(ast, name, traverse, t);
        depMap.set(p.key.value, { name, kind: isParam ? "param" : "outer", direct });
      }
      sites.push({ fp, blob: lc.arguments[0].value, enc: lc.arguments[1].value, depMap, outReg: ret.argument.property.value, isAsync: !!fn.async, ctorB });
      vmCtors.add(ctorB);
    },
  });
  if (!sites.length) return;
  ctx.detected = ctx.detected || "js-virtualizer";

  const tables = ctx.jsvTables || [];
  let lifted = 0;
  const reasons = new Map();
  const fail = (why) => reasons.set(why, (reasons.get(why) || 0) + 1);
  for (const s of sites) {
    let code;
    try { code = decodeBlob(s.blob, s.enc); } catch { fail("bytecode blob does not decode"); continue; }
    // pick the table that disassembles this blob cleanly; ambiguous => refuse
    const fits = [];
    for (const tb of tables) { try { fits.push({ tb, ins: disassemble(code, tb) }); } catch (e) { if (!(e instanceof JsvError)) throw e; } }
    if (!tables.length) { fail("opcode table unknown — add the companion VM file (its opcode numbering is shuffled per build)"); continue; }
    if (fits.length !== 1 && !(fits.length > 1 && fits.every((f) => sameTable(f.tb, fits[0].tb)))) { fail(fits.length ? "more than one VM file fits this bytecode" : "no companion VM file matches this bytecode"); continue; }
    let src;
    try {
      src = liftFunction(fits[0].ins, code.length, { deps: s.depMap, outReg: s.outReg, isAsync: s.isAsync });
    } catch (e) { if (e instanceof LiftError) { fail(e.message); continue; } throw e; }
    let bodyAst;
    try {
      const file = parse(`${s.isAsync ? "async " : ""}function __lifted__() {\n${src}\n}`);
      tidyLifted(file, { traverse, t });
      bodyAst = file.program.body[0].body;
    } catch (e) { fail("lifted code did not parse: " + e.message); continue; }
    s.fp.get("body").replaceWith(bodyAst);
    lifted++;
  }
  // the VM module import is machinery once nothing uses it
  recrawl(ast);
  for (const b of vmCtors) {
    const fresh = b.path.scope.getBinding(b.identifier.name);
    if (!fresh || fresh.referencePaths.length !== 0) continue;
    // a moved `JSVM = require(…)` assignment goes with its declaration (never leave a write to an undeclared name)
    for (const cv of fresh.constantViolations) {
      if (!cv.isAssignmentExpression() || !cv.parentPath.isExpressionStatement()) { continue; }
      cv.parentPath.remove();
    }
    if (fresh.constantViolations.some((cv) => !cv.removed && !cv.parentPath?.removed)) continue;
    if (fresh.path.parentPath.node.declarations.length === 1) fresh.path.parentPath.remove();
    else fresh.path.remove();
  }
  if (lifted) ctx.stats.jsVirtualizer = { lifted, total: sites.length };
  for (const [why, n] of reasons) ctx.errors.push(`js-virtualizer: ${n} virtualized function(s) left as-is: ${why}`);
}

const sameTable = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);

function assignedGlobals(ast, name, traverse, t) {
  let hit = false;
  traverse(ast, {
    AssignmentExpression(p) { if (t.isIdentifier(p.node.left, { name }) && !p.scope.getBinding(name)) hit = true; },
    UpdateExpression(p) { if (t.isIdentifier(p.node.argument, { name }) && !p.scope.getBinding(name)) hit = true; },
  });
  return hit;
}

/**
 * Exact cosmetic rewrites on a freshly lifted function (no closures capture
 * its locals: the lifter rejects callbacks), run on `file` = parse(...) of it.
 */
export function tidyLifted(file, { traverse, t }) {
  const boolish = (n) => t.isBinaryExpression(n) && ["==", "===", "!=", "!==", "<", "<=", ">", ">=", "instanceof", "in"].includes(n.operator)
    || t.isUnaryExpression(n, { operator: "!" }) || t.isBooleanLiteral(n);
  const negate = (n) => (t.isUnaryExpression(n, { operator: "!" }) ? n.argument : t.unaryExpression("!", n));
  traverse(file, {
    UnaryExpression: {
      exit(p) {
        // !!E -> E when E is already boolean; !!E -> E in a test position
        const n = p.node;
        if (n.operator !== "!" || !t.isUnaryExpression(n.argument, { operator: "!" })) return;
        const inner = n.argument.argument;
        const isTest = (p.parentPath.isIfStatement() || p.parentPath.isWhileStatement() || p.parentPath.isForStatement() || p.parentPath.isConditionalExpression()) && p.key === "test";
        if (boolish(inner) || isTest) p.replaceWith(inner);
      },
    },
  });
  traverse(file, {
    ForStatement: {
      exit(p) {
        // for (;;) { if (C) break; ...rest } -> while (!C) { ...rest }
        const n = p.node;
        if (n.init || n.test || n.update || !t.isBlockStatement(n.body)) return;
        const first = n.body.body[0];
        if (!t.isIfStatement(first) || first.alternate) return;
        const c = t.isBlockStatement(first.consequent) && first.consequent.body.length === 1 ? first.consequent.body[0] : first.consequent;
        if (!t.isBreakStatement(c) || c.label) return;
        p.replaceWith(t.whileStatement(negate(first.test), t.blockStatement(n.body.body.slice(1))));
      },
    },
  });
  const fn = file.program.body[0];
  const body = fn.body.body;
  // one declarator per `let`, so each can merge with its first assignment
  for (let k = 0; k < body.length; k++) {
    const s = body[k];
    if (t.isVariableDeclaration(s, { kind: "let" }) && s.declarations.length > 1) {
      body.splice(k, 1, ...s.declarations.map((d) => t.variableDeclaration("let", [d])));
    }
  }
  const refsOf = (name) => { let k = 0; traverse(file, { Identifier(q) { if (q.node.name === name && q.isReferencedIdentifier()) k++; } }); return k; };
  const countAll = (name) => { let k = 0; traverse(file, { Identifier(q) { if (q.node.name === name) k++; } }); return k; };
  // i = 0; while (i < n) { ...; i = i + 1; }  ->  for (let i = 0; i < n; i += 1) { ... }   (no `continue` inside, i used nowhere else)
  for (let k = 0; k + 1 < body.length; k++) {
    const a = body[k], w = body[k + 1];
    if (!t.isExpressionStatement(a) || !t.isAssignmentExpression(a.expression, { operator: "=" }) || !t.isIdentifier(a.expression.left) || !t.isWhileStatement(w)) continue;
    const v = a.expression.left.name;
    const wb = w.body.body, last = wb[wb.length - 1];
    if (!last || !t.isExpressionStatement(last) || !t.isAssignmentExpression(last.expression, { operator: "=" }) || !t.isIdentifier(last.expression.left, { name: v })) continue;
    const upd = last.expression.right;
    if (!t.isBinaryExpression(upd) || !["+", "-"].includes(upd.operator) || !t.isIdentifier(upd.left, { name: v }) || !t.isNumericLiteral(upd.right)) continue;
    let hasContinue = false;
    traverse(t.file(t.program([t.cloneNode(w, true)])), { noScope: true, ContinueStatement(q) { hasContinue = true; }, Function(q) { q.skip(); } });
    if (hasContinue) continue;
    // declared `let v;` at the top and used only in these three places + inside the loop
    const declIdx = body.findIndex((s) => t.isVariableDeclaration(s, { kind: "let" }) && s.declarations.some((d) => t.isIdentifier(d.id, { name: v }) && !d.init));
    let outside = 0;
    body.forEach((s, i) => { if (i !== k && i !== k + 1 && i !== declIdx) traverse(t.file(t.program([t.cloneNode(s, true)])), { noScope: true, Identifier(q) { if (q.node.name === v) outside++; } }); });
    if (declIdx < 0 || outside) continue;
    const upd2 = t.assignmentExpression(upd.operator + "=", t.identifier(v), upd.right);
    body.splice(k, 2, t.forStatement(t.variableDeclaration("let", [t.variableDeclarator(t.identifier(v), a.expression.right)]), w.test, upd2, t.blockStatement(wb.slice(0, -1))));
    const decl = body[declIdx];
    decl.declarations = decl.declarations.filter((d) => !t.isIdentifier(d.id, { name: v }));
    if (!decl.declarations.length) body.splice(declIdx, 1);
    k = -1;
  }
  // let x; ... x = E; (first mention, top level) -> let x = E;
  for (let k = 0; k < body.length; k++) {
    const s = body[k];
    if (!t.isExpressionStatement(s) || !t.isAssignmentExpression(s.expression, { operator: "=" }) || !t.isIdentifier(s.expression.left)) continue;
    const v = s.expression.left.name;
    const di = body.findIndex((d, i) => i < k && t.isVariableDeclaration(d, { kind: "let" }) && d.declarations.length === 1 && t.isIdentifier(d.declarations[0].id, { name: v }) && !d.declarations[0].init);
    if (di < 0) continue;
    let earlier = 0;
    for (let i = di + 1; i < k; i++) traverse(t.file(t.program([t.cloneNode(body[i], true)])), { noScope: true, Identifier(q) { if (q.node.name === v) earlier++; } });
    let inRhs = 0;
    traverse(t.file(t.program([t.expressionStatement(t.cloneNode(s.expression.right, true))])), { noScope: true, Identifier(q) { if (q.node.name === v) inRhs++; } });
    if (earlier || inRhs) continue;
    body[k] = t.variableDeclaration("let", [t.variableDeclarator(t.identifier(v), s.expression.right)]);
    body.splice(di, 1);
    k--;
  }
  // let/const x = E; return x;  -> return E;
  const n = body.length;
  if (n >= 2 && t.isReturnStatement(body[n - 1]) && t.isIdentifier(body[n - 1].argument) && t.isVariableDeclaration(body[n - 2]) && body[n - 2].declarations.length === 1) {
    const d = body[n - 2].declarations[0], v = body[n - 1].argument.name;
    if (t.isIdentifier(d.id, { name: v }) && d.init && countAll(v) === 2) body.splice(n - 2, 2, t.returnStatement(d.init));
  }
  // let x = E that is never reassigned -> const
  for (const s of body) {
    if (!t.isVariableDeclaration(s, { kind: "let" }) || s.declarations.length !== 1 || !s.declarations[0].init || !t.isIdentifier(s.declarations[0].id)) continue;
    const v = s.declarations[0].id.name;
    let writes = 0;
    traverse(file, { AssignmentExpression(q) { if (t.isIdentifier(q.node.left, { name: v })) writes++; }, UpdateExpression(q) { if (t.isIdentifier(q.node.argument, { name: v })) writes++; } });
    if (!writes) s.kind = "const";
  }
  return refsOf;
}
