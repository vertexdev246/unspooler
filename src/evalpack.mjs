/**
 * Eval-packer unwrapper — the `eval(atob("…"))` / `eval(unescape("…"))` /
 * `eval(decodeURIComponent("…"))` / `new Function(atob("…"))()` family plus the
 * String.fromCharCode and string-concatenation variants. Extremely common in
 * the wild (de4js's "URL encode", countless loaders and malware droppers).
 *
 * Nothing is executed. The wrapped argument is folded to its decoded string
 * with the pure-subset evaluator (atob / unescape / decodeURIComponent /
 * fromCharCode / concatenation only). Then:
 *   - a *direct* `eval("…")` at statement position is inlined — direct eval runs
 *     in the enclosing scope, so splicing its statements there is exact;
 *   - `Function("…")()` / `new Function("…")()` as a top-level statement is
 *     inlined inside an arrow IIFE — a Function body runs in the global scope,
 *     which at the top level is also what the IIFE sees;
 *   - anything else keeps the decoded string literal, so the payload is at least
 *     readable even when inlining would not be exact.
 * Runs to a fixpoint (a decoded payload may itself be eval-packed).
 */
import { createRequire } from "module";
import { makeEvaluator, Unsupported } from "./pureeval.mjs";
const require = createRequire(import.meta.url);
const parser = require("@babel/parser");
const traverse = require("@babel/traverse").default;
const t = require("@babel/types");

const parseProgram = (code) => parser.parse(code, { sourceType: "script", allowReturnOutsideFunction: true });

export function isEvalPacked(code) {
  if (!/\beval\s*\(|\bFunction\s*\(/.test(code)) return false;
  return /\beval\s*\(\s*(?:atob|unescape|decodeURIComponent|decodeURI|String\s*\.|[A-Za-z_$][\w$]*\s*\()/.test(code)
    || /\bFunction\s*\(\s*(?:atob|unescape|decodeURIComponent|String\s*\.)/.test(code);
}

/** the `arguments[0]` path of a call that is global `eval(x)` / `Function(x)` / `new Function(x)` */
function decodeArgPath(path) {
  const n = path.node;
  if (t.isCallExpression(n) && t.isIdentifier(n.callee, { name: "eval" }) && n.arguments.length === 1 && !path.scope.getBinding("eval")) return path.get("arguments.0");
  if (t.isCallExpression(n) && t.isIdentifier(n.callee, { name: "Function" }) && n.arguments.length >= 1 && !path.scope.getBinding("Function")) return path.get("arguments." + (n.arguments.length - 1));
  if (t.isNewExpression(n) && t.isIdentifier(n.callee, { name: "Function" }) && n.arguments.length >= 1 && !path.scope.getBinding("Function")) return path.get("arguments." + (n.arguments.length - 1));
  return null;
}

export function unEvalPack(ast, ctx) {
  let inlined = 0, decoded = 0;
  for (let round = 0; round < 40; round++) {
    const ev = makeEvaluator({ resolveFn: () => null, resolveMember: () => null, budget: 5_000_000 });
    let foldedThisRound = 0;
    traverse(ast, {
      "CallExpression|NewExpression"(path) {
        const argPath = decodeArgPath(path);
        if (!argPath || t.isStringLiteral(argPath.node)) return;
        let str;
        try { str = ev.expr(argPath.node, argPath); } catch (e) { if (e instanceof Unsupported || e instanceof RangeError) return; throw e; }
        if (typeof str !== "string") return;
        argPath.replaceWith(t.stringLiteral(str));
        decoded++; foldedThisRound++;
      },
    });
    const inlinedThisRound = inlineDecoded(ast);
    inlined += inlinedThisRound;
    if (!foldedThisRound && !inlinedThisRound) break;
  }
  if (inlined || decoded) ctx.stats.evalPack = { inlined, decoded };
}

function inlineDecoded(ast) {
  let n = 0;
  // direct eval("<decoded>") as a statement → the parsed statements
  traverse(ast, {
    ExpressionStatement(path) {
      const e = path.node.expression;
      if (!t.isCallExpression(e) || !t.isIdentifier(e.callee, { name: "eval" }) || e.arguments.length !== 1 || !t.isStringLiteral(e.arguments[0])) return;
      if (path.scope.getBinding("eval")) return;
      let prog;
      try { prog = parseProgram(e.arguments[0].value); } catch { return; }
      path.replaceWithMultiple(prog.program.body.length ? prog.program.body : [t.emptyStatement()]);
      n++;
    },
  });
  // Function("<decoded>")() / new Function("<decoded>")() as a top-level statement → arrow IIFE
  traverse(ast, {
    ExpressionStatement(path) {
      if (!path.parentPath.isProgram()) return;
      const call = path.node.expression;
      if (!t.isCallExpression(call) || call.arguments.length !== 0) return;
      const fn = call.callee;
      let bodyStr = null;
      if (t.isCallExpression(fn) && t.isIdentifier(fn.callee, { name: "Function" }) && fn.arguments.length === 1 && t.isStringLiteral(fn.arguments[0]) && !path.scope.getBinding("Function")) bodyStr = fn.arguments[0].value;
      else if (t.isNewExpression(fn) && t.isIdentifier(fn.callee, { name: "Function" }) && fn.arguments.length === 1 && t.isStringLiteral(fn.arguments[0]) && !path.scope.getBinding("Function")) bodyStr = fn.arguments[0].value;
      if (bodyStr === null) return;
      let prog;
      try { prog = parseProgram(bodyStr); } catch { return; }
      path.replaceWith(t.expressionStatement(t.callExpression(t.arrowFunctionExpression([], t.blockStatement(prog.program.body)), [])));
      n++;
    },
  });
  return n;
}
