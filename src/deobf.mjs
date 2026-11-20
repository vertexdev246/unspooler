/**
 * JS-Confuser LOW-preset deobfuscator.
 *
 * Reverses the transformations in src/order.ts in reverse application
 * order, using only structural shape-matching against the exact templates
 * JS-Confuser generates. Constructs that don't match a known obfuscator
 * shape are left untouched (no guessing).
 */
import * as t from "@babel/types";
import { base91Decode, bytesToString } from "./util.mjs";
import { reverseControlFlowFlattening } from "./cff.mjs";
import { reverseStringArray, cleanObfioHelpers, reverseObfioStructure } from "./obfio.mjs";
import { detectObfuscator } from "./detect.mjs";
import { isJsfuck, unJsfuck } from "./jsfuck.mjs";
import { unJsVirtualizer } from "./jsvirt-pass.mjs";
import { isJsdefender, peelJsdefender, foldJsdefenderHelpers, eliminateDeadDeclarations } from "./jsdefender.mjs";
import { unEvalPack } from "./evalpack.mjs";
import { unflattenJsdefender, tidyLoops } from "./jsd-cff.mjs";
import { opNamesFromVmSource } from "./jsvirt.mjs";
import { unpackPacker } from "./packer.mjs";
import { decodeJjencode, decodeAaencode } from "./jjencode.mjs";
import { isJfogs, unJfogs } from "./jfogs.mjs";
import { unGnirts } from "./gnirts.mjs";

const require = (await import("module")).createRequire(import.meta.url);
export const parser = require("@babel/parser");
export const traverse = require("@babel/traverse").default;
export const babelGenerate = require("@babel/generator").default;

export const parse = (code) =>
  parser.parse(code, {
    allowReturnOutsideFunction: true,
    allowAwaitOutsideFunction: true,
    sourceType: "unambiguous",
  });

export const generate = (ast, opts = {}) =>
  babelGenerate(ast, {
    compact: false,
    minified: false,
    retainLines: false,
    comments: true,
    ...opts,
  }).code;

// --------------------------------------------------- traversal helpers

/** walk a node subtree manually (no babel scope machinery) */
function walkNodes(root, visit) {
  const stack = [{ node: root, parents: [] }];
  while (stack.length) {
    const { node: cur, parents } = stack.pop();
    if (cur === null || cur === undefined || typeof cur !== "object") continue;
    if (Array.isArray(cur)) {
      for (const el of cur) stack.push({ node: el, parents });
      continue;
    }
    if (typeof cur.type === "string") visit(cur, parents);
    const childParents = [cur, ...parents];
    for (const key of Object.keys(cur)) {
      if (key.startsWith("$") || key === "loc" || key === "start" || key === "end" || key === "leadingComments" || key === "trailingComments" || key === "innerComments")
        continue;
      stack.push({ node: cur[key], parents: childParents });
    }
  }
}

/** visit every node of an arbitrary subtree */
function subTraverse(node, visitors) {
  if (node === null || node === undefined) return;
  walkNodes(node, (n, parents) => {
    const v = visitors[n.type];
    if (typeof v === "function") v({ node: n, parent: parents[0], parents });
    else if (v && typeof v.enter === "function") v.enter({ node: n, parent: parents[0], parents });
  });
}
/** visit a statement list */
function subTraverseList(statements, visitors) {
  return subTraverse({ type: "BlockStatement", body: statements || [] }, visitors);
}

/** real writes to a binding: babel lists a block-level function declaration
 * as a constant violation of its own binding */
function writesOf(b) {
  return b.constantViolations.filter((cv) => cv.node !== b.path.node);
}
/** binding a FunctionDeclaration path defines — also when it shares a name
 *  with a param (the declaration replaces it on entry; babel then lists the
 *  declaration as the param's only write). null if anything else writes it. */
function fnDeclBinding(path) {
  const b = path.parentPath.scope.getBinding(path.node.id.name);
  if (!b) return null;
  if (b.path.node === path.node) return writesOf(b).length === 0 ? b : null;
  if (b.kind === "param" && b.constantViolations.length === 1 && b.constantViolations[0].node === path.node) return b;
  return null;
}
function recrawl(ast) {
  traverse(ast, {
    Program: {
      enter(path) {
        path.scope.crawl();
      },
    },
  });
}

// ------------------------------------------------------------ helpers

/** numeric literal value, incl. `-N` */
function numValue(n) {
  if (t.isNumericLiteral(n)) return n.value;
  if (t.isUnaryExpression(n, { operator: "-" }) && t.isNumericLiteral(n.argument)) return -n.argument.value;
  return null;
}
function simpleValueOf(node) {
  if (t.isStringLiteral(node)) return { type: "string", value: node.value };
  if (t.isNumericLiteral(node)) return { type: "number", value: node.value };
  if (t.isBooleanLiteral(node)) return { type: "bool", value: node.value };
  if (t.isNullLiteral(node)) return { type: "null", value: null };
  if (t.isIdentifier(node, { name: "undefined" }))
    return { type: "undefined", value: undefined };
  if (
    t.isUnaryExpression(node, { prefix: true, operator: "!" }) &&
    t.isNumericLiteral(node.argument)
  )
    return { type: "bool", value: node.argument.value === 0 };
  if (
    t.isUnaryExpression(node, { prefix: true, operator: "-" }) &&
    t.isNumericLiteral(node.argument)
  )
    return { type: "number", value: -node.argument.value };
  return null;
}

function valueNode(simple) {
  switch (simple.type) {
    case "string":
      return t.stringLiteral(simple.value);
    case "number": {
      const v = simple.value;
      return v < 0 || Object.is(v, -0)
        ? t.unaryExpression("-", t.numericLiteral(Object.is(v, -0) ? 0 : -v), true)
        : t.numericLiteral(v);
    }
    case "bool":
      return t.booleanLiteral(simple.value);
    case "null":
      return t.nullLiteral();
    case "undefined":
      return t.identifier("undefined");
  }
}

/** property string of a member: a["slice"] or a.slice -> "slice" */
function memberPropString(node) {
  if (!node || !t.isMemberExpression(node)) return null;
  const prop = node.property;
  if (t.isStringLiteral(prop) && node.computed) return prop.value;
  if (t.isIdentifier(prop) && !node.computed) return prop.name;
  return null;
}

function simplePropKey(prop) {
  if (!t.isObjectProperty(prop)) return null;
  if (prop.computed) {
    if (t.isStringLiteral(prop.key)) return prop.key.value;
    return null;
  }
  if (t.isStringLiteral(prop.key)) return prop.key.value;
  if (t.isIdentifier(prop.key)) return prop.key.name;
  if (t.isNumericLiteral(prop.key)) return String(prop.key.value);
  return null;
}

function cloneNode(node) {
  return JSON.parse(JSON.stringify(node));
}

/** base91 decoder function: `* 91`, `8191`, a string table var — own body only */
function isBase91DecoderNode(fn) {
  if (!fn || !t.isFunction(fn) || !t.isBlockStatement(fn.body)) return false;
  let has91 = false,
    has8191 = false,
    hasTable = false;
  walkNodes(fn.body, (n, parents) => {
    if (parents.some((p) => t.isFunction(p))) return;
    if (t.isBinaryExpression(n, { operator: "*" }) && t.isNumericLiteral(n.right, { value: 91 })) has91 = true;
    else if (t.isNumericLiteral(n, { value: 8191 })) has8191 = true;
    else if (
      (t.isVariableDeclarator(n) && t.isStringLiteral(n.init) && t.isIdentifier(n.id)) ||
      (t.isAssignmentExpression(n, { operator: "=" }) && t.isIdentifier(n.left) && t.isStringLiteral(n.right))
    )
      hasTable = true;
  });
  return has91 && has8191 && hasTable;
}

function nodeCode(node) {
  try {
    return babelGenerate(node, { compact: true }).code;
  } catch {
    return "";
  }
}

// ============================================================== passes

const passes = [];
const pass = (name, fn) => passes.push({ name, fn });

/* ================================================================== *
 * 0. un-Pack (MEDIUM+): the whole program became                      *
 *    Function("O", "<code>")({ get "a"(){return g}, set "a"(O){return  *
 *    g = O}, get "t"(){return typeof g} })                             *
 *    with every global access inside rewritten to O["a"] / O["t"].     *
 *    Restored as an IIFE: inside Function() the code's vars were       *
 *    function-local, so hoisting them to the top level would turn them *
 *    into real globals (observable). The IIFE keeps that exact.        *
 * ================================================================== */
pass("unPack", (ast, ctx) => {
  const body = ast.program.body;
  const idx = body.findIndex(
    (st) =>
      t.isExpressionStatement(st) &&
      t.isCallExpression(st.expression) &&
      t.isCallExpression(st.expression.callee) &&
      t.isIdentifier(st.expression.callee.callee, { name: "Function" }) &&
      st.expression.callee.arguments.length === 2 &&
      st.expression.callee.arguments.every((a) => t.isStringLiteral(a)) &&
      st.expression.arguments.length === 1 &&
      t.isObjectExpression(st.expression.arguments[0]),
  );
  if (idx < 0) return;
  if (body.length !== 1) return void ctx.errors.push("unPack: left packed (statements outside the pack call)");
  const call = body[idx].expression;
  const objName = call.callee.arguments[0].value;
  const innerCode = call.callee.arguments[1].value;
  if (!t.isValidIdentifier(objName)) return;

  // property -> { get: name | {typeof: name}, set: name }
  const props = new Map();
  for (const p of call.arguments[0].properties) {
    const key = t.isObjectMethod(p) ? (t.isStringLiteral(p.key) ? p.key.value : t.isIdentifier(p.key) && !p.computed ? p.key.name : null) : null;
    if (key === null || p.body.body.length !== 1 || !t.isReturnStatement(p.body.body[0])) return;
    const ret = p.body.body[0].argument;
    const entry = props.get(key) || {};
    if (p.kind === "get" && p.params.length === 0 && t.isIdentifier(ret)) entry.get = ret.name;
    else if (p.kind === "get" && p.params.length === 0 && t.isUnaryExpression(ret, { operator: "typeof" }) && t.isIdentifier(ret.argument))
      entry.typeofOf = ret.argument.name;
    else if (
      p.kind === "set" &&
      p.params.length === 1 &&
      t.isIdentifier(p.params[0]) &&
      t.isAssignmentExpression(ret, { operator: "=" }) &&
      t.isIdentifier(ret.left) &&
      t.isIdentifier(ret.right, { name: p.params[0].name })
    )
      entry.set = ret.left.name;
    else return;
    props.set(key, entry);
  }
  for (const e of props.values()) if (e.set && e.get && e.set !== e.get) return;

  let inner;
  try {
    inner = parse(innerCode);
  } catch (e) {
    ctx.errors.push(`unPack: packed code does not parse: ${e.message}`);
    return;
  }

  // rewrite O["k"] sites; validate every one first
  const sites = [];
  let bad = null;
  traverse(inner, {
    Program(p) {
      p.scope.crawl();
    },
    MemberExpression(p) {
      if (!t.isIdentifier(p.node.object, { name: objName })) return;
      if (p.scope.getBinding(objName)) return; // a local shadows the pack object
      const key = memberPropString(p.node);
      const e = key === null ? null : props.get(key);
      if (!e) return void (bad = bad || `unknown pack property ${key}`);
      const name = e.typeofOf || e.get || e.set;
      if (p.scope.getBinding(name)) return void (bad = bad || `restored global ${name} would be shadowed`);
      const isWrite =
        (p.parentPath.isAssignmentExpression() && p.key === "left") ||
        p.parentPath.isUpdateExpression() ||
        (p.parentPath.isForXStatement() && p.key === "left");
      const isRead = !(p.parentPath.isAssignmentExpression({ operator: "=" }) && p.key === "left");
      if (p.parentPath.isUnaryExpression({ operator: "delete" })) return void (bad = bad || "delete of a packed global");
      if (e.typeofOf) {
        if (isWrite) return void (bad = bad || "write to a typeof mapping");
      } else {
        if (isWrite && !e.set) return void (bad = bad || `write to read-only mapping ${key}`);
        if (isRead && !e.get) return void (bad = bad || `read of write-only mapping ${key}`);
      }
      sites.push({ p, e, name });
    },
  });
  if (bad) return void ctx.errors.push(`unPack: left packed (${bad})`);
  for (const { p, e, name } of sites)
    p.replaceWith(e.typeofOf ? t.unaryExpression("typeof", t.identifier(name), true) : t.identifier(name));
  // any remaining use of the pack object (e.g. passed around) -> keep packed
  let leftover = false;
  traverse(inner, {
    Identifier(p) {
      if (p.node.name === objName && !p.scope.getBinding(objName) && p.isReferencedIdentifier()) leftover = true;
    },
  });
  if (leftover) return void ctx.errors.push("unPack: left packed (pack object used directly)");

  // pack turned the last expression statement into `return expr;`
  const ib = inner.program.body;
  const last = ib.at(-1);
  if (t.isReturnStatement(last) && last.argument) ib[ib.length - 1] = t.expressionStatement(last.argument);

  // analyse the inner code at top level; `rePack` wraps it back up at the end
  ast.program.body = ib;
  ast.program.directives = inner.program.directives;
  ctx.packed = true;
  ctx.stats.pack = { globals: props.size };
});

/* ================================================================== *
 * 0b. un-StringEncoding (HIGH): "abc" was written as "\x61\x62\x63" /  *
 *     "a…". Same value — drop the escaped raw text so the code    *
 *     (and every text-based check downstream) sees the plain string.   *
 * ================================================================== */
pass("unStringEncoding", (ast, ctx) => {
  let cleared = 0;
  traverse(ast, {
    "StringLiteral|DirectiveLiteral"(p) {
      const raw = p.node.extra?.raw;
      if (raw && /\\(x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|u\{)/.test(raw)) {
        delete p.node.extra;
        cleared++;
      }
    },
  });
  ctx.stats.stringEncoding = { cleared };
});

/* ================================================================== *
 * 0a2. eval-packer: fold eval(atob("…")) / Function(unescape("…"))() … *
 *     to the decoded payload and inline direct eval / top-level        *
 *     Function(). Nothing is executed (pure-subset evaluator). Runs     *
 *     early so a decoded payload goes through the rest of the pipeline. *
 * ================================================================== */
pass("unEvalPack", (ast, ctx) => {
  unEvalPack(ast, ctx);
});

/* ================================================================== *
 * 0b. un-gnirts (LOW): fold gnirts' pure-arithmetic string rebuilders  *
 *     back into literals. gnirts only touches code between            *
 *     /* @mangle *\/ … /* @/mangle *\/ directives: string literals     *
 *     become charcode-IIFE / base-36 chains, and `T === 'str'` checks *
 *     become reversed indexOf/RegExp `&&` chains. All folds are exact *
 *     static evaluations; shapes that don't match are left untouched. *
 * ================================================================== */
pass("unGnirts", (ast, ctx) => {
  const folded = unGnirts(ast);
  if (folded) ctx.stats.gnirts = { folded };
});

/* ================================================================== *
 * 0c. un-name-restore (js-obfuscator.com): its Replace Names feature  *
 *     renames every function and ships a helper that restores the     *
 *     original .name at runtime:                                      *
 *       function d(c, d2) { try { var b =                             *
 *         Object.getOwnPropertyDescriptor(c, "name");                 *
 *         if (!b || !b.writable && !b.enumerable && b.configurable && *
 *             typeof b.value == "string")                             *
 *           Object.defineProperty(c, "name",                          *
 *             { value: d2, configurable: true });                     *
 *       } catch (e) {} return c; }                                    *
 *     with call sites `EXPORT = d(fn, "origName");`. Fold: rename fn  *
 *     back to origName (safe, shadow-aware via babel scopes), drop    *
 *     the assignments and the helper. Any shape that deviates → the   *
 *     helper is left exactly as-is (identical behavior).              *
 * ================================================================== */
pass("unJsobNameRestore", (ast, ctx) => {
  // ---- exact helper shape -------------------------------------------
  //   function H(p0, p1) {
  //     try {
  //       var d = Object.getOwnPropertyDescriptor(p0, "name");
  //       if (!d || (!d.writable && !d.enumerable && d.configurable &&
  //                  typeof d.value == "string")) {
  //         Object.defineProperty(p0, "name", { value: p1, configurable: true });
  //       }
  //     } catch (e) {}
  //     return p0;
  //   }
  const isHelper = (fn) => {
    if (!t.isFunctionDeclaration(fn) || fn.params.length !== 2 ||
      !fn.params.every((p) => t.isIdentifier(p))) return false;
    const [p0, p1] = fn.params.map((p) => p.name);
    const realBody = fn.body.body.filter((s) => !t.isEmptyStatement(s));
    if (realBody.length !== 2) return false;
    const [trySt, ret] = realBody;
    if (!t.isTryStatement(trySt) || trySt.finalizer || !trySt.handler || !t.isReturnStatement(ret) ||
      !t.isIdentifier(ret.argument, { name: p0 })) return false;
    if (!t.isBlockStatement(trySt.handler.body) || trySt.handler.body.body.length !== 0) return false;
    if (trySt.block.body.length !== 2) return false;
    const [varSt, ifSt] = trySt.block.body;
    if (!t.isVariableDeclaration(varSt, { kind: "var" }) || varSt.declarations.length !== 1 ||
      !t.isIdentifier(varSt.declarations[0].id) || !t.isIfStatement(ifSt) || ifSt.alternate) return false;
    const desc = varSt.declarations[0].id.name;
    const tmpInit = varSt.declarations[0].init;
    if (!t.isCallExpression(tmpInit) || !t.isMemberExpression(tmpInit.callee) || tmpInit.callee.computed ||
      !t.isIdentifier(tmpInit.callee.object, { name: "Object" }) ||
      !t.isIdentifier(tmpInit.callee.property, { name: "getOwnPropertyDescriptor" }) ||
      tmpInit.arguments.length !== 2 || !t.isIdentifier(tmpInit.arguments[0], { name: p0 }) ||
      !t.isStringLiteral(tmpInit.arguments[1], { value: "name" })) return false;
    // test: !desc || (!desc.writable && !desc.enumerable && desc.configurable && typeof desc.value == "string")
    const test = ifSt.test;
    if (!t.isLogicalExpression(test, { operator: "||" })) return false;
    if (!t.isUnaryExpression(test.left, { operator: "!" }) || !t.isIdentifier(test.left.argument, { name: desc })) return false;
    const checks = [];
    for (let cur = test.right; ; ) {
      if (t.isLogicalExpression(cur, { operator: "&&" })) { checks.unshift(cur.right); cur = cur.left; }
      else { checks.unshift(cur); break; }
    }
    if (checks.length !== 4) return false;
    const [writable, enumerable, configurable, valueString] = checks;
    const isDescMember = (n, prop) => t.isMemberExpression(n) && !n.computed &&
      t.isIdentifier(n.object, { name: desc }) && t.isIdentifier(n.property, { name: prop });
    if (!t.isUnaryExpression(writable, { operator: "!" }) || !isDescMember(writable.argument, "writable")) return false;
    if (!t.isUnaryExpression(enumerable, { operator: "!" }) || !isDescMember(enumerable.argument, "enumerable")) return false;
    if (!isDescMember(configurable, "configurable")) return false;
    // typeof desc.value == "string" (or ===)
    if (!t.isBinaryExpression(valueString) || !["==", "==="].includes(valueString.operator) ||
      !t.isUnaryExpression(valueString.left, { operator: "typeof" }) ||
      !isDescMember(valueString.left.argument, "value") ||
      !t.isStringLiteral(valueString.right, { value: "string" })) return false;
    if (!t.isBlockStatement(ifSt.consequent) || ifSt.consequent.body.length !== 1 ||
      !t.isExpressionStatement(ifSt.consequent.body[0])) return false;
    const expr = ifSt.consequent.body[0].expression;
    // Object.defineProperty(p0, "name", { value: p1, configurable: true })
    if (!t.isCallExpression(expr) || !t.isMemberExpression(expr.callee) || expr.callee.computed ||
      !t.isIdentifier(expr.callee.object, { name: "Object" }) ||
      !t.isIdentifier(expr.callee.property, { name: "defineProperty" }) ||
      expr.arguments.length !== 3 || !t.isIdentifier(expr.arguments[0], { name: p0 }) ||
      !t.isStringLiteral(expr.arguments[1], { value: "name" }) ||
      !t.isObjectExpression(expr.arguments[2]) || expr.arguments[2].properties.length !== 2) return false;
    const [valueProp, configProp] = expr.arguments[2].properties;
    if (!t.isObjectProperty(valueProp) || !t.isIdentifier(valueProp.key, { name: "value" }) ||
      !t.isIdentifier(valueProp.value, { name: p1 })) return false;
    if (!t.isObjectProperty(configProp) || !t.isIdentifier(configProp.key, { name: "configurable" }) ||
      !t.isBooleanLiteral(configProp.value, { value: true })) return false;
    return true;
  };

  let helperPath = null;
  traverse(ast, {
    FunctionDeclaration(p) {
      if (!helperPath && isHelper(p.node)) { helperPath = p; p.stop(); }
    },
  });
  if (!helperPath) return;
  const helperName = helperPath.node.id.name;

  // ---- call sites:  EXPORT = H(FN, "origName");
  const sites = [];
  let foreignUse = false;
  traverse(ast, {
    ExpressionStatement(p) {
      const e = p.node.expression;
      if (t.isAssignmentExpression(e, { operator: "=" }) && t.isIdentifier(e.left) &&
        t.isCallExpression(e.right) && t.isIdentifier(e.right.callee, { name: helperName }) &&
        e.right.arguments.length === 2 && t.isIdentifier(e.right.arguments[0]) &&
        t.isStringLiteral(e.right.arguments[1])) {
        sites.push({
          path: p, fn: e.right.arguments[0].name, orig: e.right.arguments[1].value,
          export: e.left.name,
        });
      }
    },
    ReferencedIdentifier(p) {
      if (p.node.name !== helperName) return;
      if (p.getFunctionParent()?.node === helperPath.node) return; // helper internals (its own params etc.)
      if (t.isCallExpression(p.parent) && p.key === "callee") return; // site callee (or foreign call)
      if (t.isFunctionDeclaration(p.parent) && p.parent.id === p.node) return; // the helper's own name
      foreignUse = true; // any other reference (including foreign calls)
    },
  });
  if (foreignUse || !sites.length) return; // helper used unexpectedly → leave as-is

  // ---- every site must resolve to a safely renamable function declaration
  const isInside = (block, path) => {
    for (let cur = path; cur; cur = cur.parentPath) if (cur.node === block) return true;
    return false;
  };
  const renames = [];
  for (const site of sites) {
    const binding = site.path.scope.getBinding(site.fn);
    if (!binding || !binding.path.isFunctionDeclaration()) return; // leave the helper untouched
    const scope = binding.scope;
    if (scope.hasOwnBinding(site.orig)) return; // duplicate declaration in that scope
    // an existing outer binding of the same name is only tolerable when it is
    // not read/written inside the scope that the rename would shadow
    const outer = scope.getBinding(site.orig);
    if (outer) {
      for (const ref of outer.referencePaths) {
        if (isInside(scope.block, ref)) return;
      }
      for (const v of outer.constantViolations) {
        if (sites.some((s) => isInside(s.path.node, v))) continue; // dropped assignments
        if (isInside(scope.block, v)) return;
      }
    }
    renames.push({ scope, from: site.fn, to: site.orig });
  }
  // any free (unbound) reference to the target names anywhere would change meaning
  const refNames = new Set();
  traverse(ast, {
    ReferencedIdentifier(p) {
      if (!p.scope.hasBinding(p.node.name)) refNames.add(p.node.name);
    },
  });
  for (const r of renames) {
    if (refNames.has(r.to)) return; // free refs to `r.to` would get shadowed
  }

  // ---- plan the global-export restoration -------------------------------
  // The dropped assignment `X = H(FN, "orig")` also set X (the helper returns
  // its first argument). When X === orig the right repair is to move the
  // renamed function declaration out to program scope in place of the
  // `var X;` declaration; otherwise the assignment must survive as `X = FN;`.
  // Everything is analyzed before any mutation; one unfitting shape aborts the
  // whole transform and leaves the helper exactly as it was.
  const moveOuts = []; // X === orig: fn decl moves to program scope
  const keepAssigns = []; // X !== orig: `X = FN;` keeps the assignment
  const droppedSites = [];
  const movedNames = new Set();
  for (const site of sites) {
    const binding = site.path.scope.getBinding(site.fn);
    if (!binding || !binding.path.isFunctionDeclaration()) return;
    if (site.export !== site.orig) { keepAssigns.push(site); continue; }

    // X === orig → the function must be movable to program scope:
    // 1. the fn decl is a direct child of a program-level IIFE body
    const fnPath = binding.path;
    const bodyBlock = fnPath.parentPath;
    const iifeFn = bodyBlock.parentPath;
    const iifeCall = iifeFn.parentPath;
    const iifeStmt = iifeCall.parentPath;
    if (!bodyBlock.isBlockStatement() || !iifeFn.isFunctionExpression() ||
      iifeFn.node.body !== bodyBlock.node ||
      !iifeCall.isCallExpression() || iifeCall.node.callee !== iifeFn.node ||
      !iifeStmt.isExpressionStatement() || !iifeStmt.parentPath.isProgram()) return;
    // 2. X is a program-scope `var X;` with no initializer
    const xb = site.path.scope.getBinding(site.export);
    if (!xb || !xb.path.isVariableDeclarator() || xb.path.node.init != null) return;
    if (xb.scope.block.type !== "Program" || !xb.path.parentPath.parentPath.isProgram()) return;
    // 3. no reads of X anywhere, and no writes to X other than the dropped
    //    assignments (a read could see undefined vs the hoisted function)
    if (xb.referencePaths.length) return;
    for (const v of xb.constantViolations) {
      if (sites.some((s) => isInside(s.path.node, v))) continue;
      return;
    }
    // 4. the fn references nothing bound inside the IIFE outside itself
    let bad = false;
    fnPath.traverse({
      ReferencedIdentifier(p) {
        if (bad) return p.stop();
        const b = p.scope.getBinding(p.node.name);
        if (!b) return; // global/free — fine, program scope sees the same
        if (isInside(fnPath.node, b.path)) return; // fn's own params/locals/self
        if (isInside(bodyBlock.node, b.path)) { bad = true; p.stop(); }
      },
    });
    if (bad) return;
    // 5. one function per export name
    if (movedNames.has(site.orig)) return;
    movedNames.add(site.orig);
    moveOuts.push({ fnPath, dclPath: xb.path, iifeStmt });
    droppedSites.push(site);
  }

  // ---- mutate -----------------------------------------------------------
  for (const r of renames) r.scope.rename(r.from, r.to);
  for (const site of keepAssigns) {
    // `X = H(FN, "orig")` → `X = FN;` (the callee value is what X received)
    const fnName = site.path.node.expression.right.arguments[0].name; // renamed
    site.path.replaceWith(
      t.expressionStatement(
        t.assignmentExpression("=", t.identifier(site.export), t.identifier(fnName))));
  }
  for (const m of moveOuts) {
    // drop the program-scope `var X;` declarator
    const declStmt = m.dclPath.parentPath;
    if (declStmt.node.declarations.length === 1) declStmt.remove();
    else m.dclPath.remove();
    // move the renamed function declaration out to program scope
    const fnNode = t.cloneNode(m.fnPath.node, true);
    m.iifeStmt.insertBefore(fnNode);
    m.fnPath.remove();
  }
  for (const site of droppedSites) site.path.remove();
  helperPath.remove();
  ctx.stats.jsobNameRestore = { functions: renames.length, exported: moveOuts.length };
});

/* ================================================================== *
 * 1. split grouped var declarations (minify merged same-kind decls)    *
 * ================================================================== */
pass("splitVarDecls", (ast) => {
  traverse(ast, {
    VariableDeclaration: {
      exit(path) {
        if (path.node.declarations.length < 2) return;
        const { parent } = path;
        if (
          t.isForStatement(parent) ||
          t.isForInStatement(parent) ||
          t.isForOfStatement(parent) ||
          t.isExportDeclaration(parent)
        )
          return;
        path.replaceWithMultiple(
          path.node.declarations.map((d) =>
            t.variableDeclaration(path.node.kind, [d]),
          ),
        );
        path.skip();
      },
    },
  });
});

/* ================================================================== *
 * split statement-level comma sequences early: `a, b;` -> `a; b;` and   *
 * `return a, b;` -> `a; return b;` (exact) so shape matchers see the    *
 * statements the obfuscators merged ("simplify" in obfuscator.io).     *
 * ================================================================== */
pass("splitSequences", (ast, ctx) => {
  // obfuscator.io only: JS-Confuser's CFF reverser relies on comma-merged
  // state updates (normalize splits sequences for everyone at the end)
  if (ctx.detected !== "javascript-obfuscator") return;
  const inList = (p) => p.parentPath.isBlockStatement() || p.parentPath.isProgram() || p.parentPath.isSwitchCase();
  traverse(ast, {
    ExpressionStatement: {
      exit(path) {
        const e = path.node.expression;
        if (!t.isSequenceExpression(e) || !inList(path)) return;
        path.replaceWithMultiple(e.expressions.map((x) => t.expressionStatement(x)));
      },
    },
    "ReturnStatement|ThrowStatement": {
      exit(path) {
        const e = path.node.argument;
        if (!t.isSequenceExpression(e) || !inList(path)) return;
        const last = e.expressions[e.expressions.length - 1];
        path.replaceWithMultiple([
          ...e.expressions.slice(0, -1).map((x) => t.expressionStatement(x)),
          path.isReturnStatement() ? t.returnStatement(last) : t.throwStatement(last),
        ]);
      },
    },
  });
});

/* ================================================================== *
 * obfuscator.io (javascript-obfuscator) string array — see lib/obfio.mjs *
 * ================================================================== */
pass("obfioStringArray", (ast, ctx) => {
  reverseStringArray(ast, ctx);
});
pass("obfioHelpers", (ast, ctx) => {
  cleanObfioHelpers(ast, ctx);
});
pass("obfioStructure", (ast, ctx) => {
  reverseObfioStructure(ast, ctx, { foldNumbers: ctx.detected === "javascript-obfuscator" || ctx.detected === "jsdefender" });
});

/* ================================================================== *
 * 2. un-AstScrambler                                                  *
 *    function N(){ N = function(){}; }  appended at program end; all   *
 *    expression statements got folded into N(a,b,c) calls. The first   *
 *    call reassigns N to a no-op, so N(a,b,c) === a;b;c; exactly.      *
 * ================================================================== */
pass("unAstScrambler", (ast, ctx) => {
  let astFnName = null;
  for (const st of ast.program.body) {
    if (!t.isFunctionDeclaration(st)) continue;
    const node = st;
    if (node.params.length !== 0 || !t.isIdentifier(node.id)) continue;
    if (node.body.body.length !== 1) continue;
    const stmt = node.body.body[0];
    if (
      !t.isExpressionStatement(stmt) ||
      !t.isAssignmentExpression(stmt.expression, { operator: "=" }) ||
      !t.isIdentifier(stmt.expression.left, { name: node.id.name })
    )
      continue;
    const rhs = stmt.expression.right;
    if (
      !t.isFunctionExpression(rhs) ||
      !t.isBlockStatement(rhs.body) ||
      rhs.body.body.length !== 0 ||
      rhs.params.length !== 0
    )
      continue;
    astFnName = node.id.name;
    break;
  }
  if (!astFnName) return;
  const stubNode = ast.program.body.find(
    (st) => t.isFunctionDeclaration(st) && st.id.name === astFnName,
  );
  const stubBinding = () => {
    let b = null;
    traverse(ast, {
      Program(p) {
        p.scope.crawl();
        b = p.scope.getOwnBinding(astFnName);
        p.stop();
      },
    });
    return b && b.path.node === stubNode ? b : null;
  };

  let calls = 0;
  let changed = true;
  let guard = 0;
  while (changed && guard++ < 500) {
    changed = false;
    const b = stubBinding();
    if (!b) break;
    // innermost / last first, so pending paths stay valid while expanding
    const refs = [...b.referencePaths].sort((x, y) => (y.node.start ?? 0) - (x.node.start ?? 0));
    for (const rp of refs) {
      // only `N(a, b, …);` statements; binding-checked (names are reused)
      const call = rp.parentPath;
      if (!call.isCallExpression() || rp.key !== "callee") continue;
      const stmt = call.parentPath;
      if (!stmt.isExpressionStatement() || stmt.removed) continue;
      if (call.node.arguments.some((a) => !t.isExpression(a))) continue;
      calls += call.node.arguments.length;
      stmt.replaceWithMultiple(call.node.arguments.map((a) => t.expressionStatement(a)));
      changed = true;
    }
  }
  // the stub only reassigns itself: drop it once nothing calls it
  const b = stubBinding();
  if (b && b.referencePaths.every((rp) => rp.isDescendant(b.path)))
    ast.program.body.splice(ast.program.body.indexOf(stubNode), 1);
  ctx.stats.astScrambler = { expressions: calls };
});

/* ================================================================== *
 * 3. un-Minify cosmetics: !0->true, void 0->undefined, 1/0->Infinity   *
 * ================================================================== */
pass("unMinify", (ast) => {
  traverse(ast, {
    UnaryExpression(path) {
      if (path.node.operator === "!") {
        if (t.isNumericLiteral(path.node.argument))
          path.replaceWith(
            t.booleanLiteral(path.node.argument.value === 0, ),
          );
      } else if (
        path.node.operator === "void" &&
        t.isNumericLiteral(path.node.argument, { value: 0 })
      ) {
        path.replaceWith(t.identifier("undefined"));
      }
    },
    BinaryExpression(path) {
      if (path.node.operator !== "/") return;
      if (
        t.isNumericLiteral(path.node.left, { value: 1 }) &&
        t.isNumericLiteral(path.node.right, { value: 0 })
      )
        path.replaceWith(t.identifier("Infinity"));
    },
  });
});

/* ================================================================== *
 * 4. un-MovedDeclarations                                             *
 *    `var x;` hoisted to the top of its own block; the original        *
 *    position became `x = <init>;` (or a bare for-in/of head).         *
 *    Inline the init back when provably unambiguous.                   *
 * ================================================================== */
pass("unMovedDeclarations", (ast, ctx) => {
  let inlined = 0;
  traverse(ast, {
    "Program|BlockStatement": {
      exit(blockPath) {
        const node = blockPath.node;
        if (!(t.isProgram(node) || t.isBlockStatement(node))) return;
        const bodyPath = blockPath.get("body");
        if (!Array.isArray(bodyPath) || bodyPath.length === 0) return;

        // leading bare var decls (the hoisted pile)
        const hoisted = new Map(); // name -> stmt path
        for (const stPath of bodyPath) {
          const st = stPath.node;
          if (t.isFunctionDeclaration(st) || t.isImportDeclaration(st))
            continue;
          if (!t.isVariableDeclaration(st) || st.kind !== "var") break;
          if (st.declarations.length !== 1) break;
          const d = st.declarations[0];
          if (!t.isIdentifier(d.id) || d.init !== null) break;
          hoisted.set(d.id.name, stPath);
        }
        if (hoisted.size === 0) return;
        const hoistedNames = new Set(hoisted.keys());

        // first direct-child write at THIS statement-list level:
        // `x = init;` or a for-loop head `for (x = init; …)`
        const sites = new Map(); // name -> { path, init, isFor }
        for (const stPath of bodyPath) {
          let expr = null;
          let isFor = false;
          if (stPath.isExpressionStatement()) expr = stPath.node.expression;
          else if (stPath.isForStatement()) {
            expr = stPath.node.init;
            isFor = true;
          }
          if (
            t.isAssignmentExpression(expr, { operator: "=" }) &&
            t.isIdentifier(expr.left) &&
            hoistedNames.has(expr.left.name) &&
            !sites.has(expr.left.name)
          )
            sites.set(expr.left.name, { path: stPath, init: expr.right, isFor });
        }

        for (const [name, hoistedPath] of hoisted) {
          const site = sites.get(name);
          if (!site) continue;
          const sitePath = site.path;
          const idx = bodyPath.indexOf(sitePath);
          if (idx < 0) continue;

          // any use of this same binding before the assignment keeps the
          // hoisted form (var hoisting makes both exact; this is readability)
          const nameBinding = sitePath.scope.getBinding(name);
          let earlyRef = false;
          if (nameBinding) {
            for (let i = 0; i < idx && !earlyRef; i++) {
              const prev = bodyPath[i].node;
              if (
                t.isVariableDeclaration(prev) &&
                prev.declarations.length === 1 &&
                t.isIdentifier(prev.declarations[0].id) &&
                prev.declarations[0].init === null
              )
                continue; // bare decl (no reads)
              bodyPath[i].traverse({
                Identifier(p) {
                  if (p.node.name === name && p.scope.getBinding(name) === nameBinding)
                    earlyRef = true;
                },
              });
            }
          }
          if (earlyRef) continue;
          const decl = t.variableDeclaration("var", [
            t.variableDeclarator(t.identifier(name), site.init),
          ]);
          // restore `var x = init;` / `for (var x = init; …)` at the write
          if (site.isFor) sitePath.node.init = decl;
          else sitePath.replaceWith(decl);
          hoistedPath.remove();
          inlined++;
        }
        ctx.stats.movedDeclarations = { inlined };
      },
    },
    "ForInStatement|ForOfStatement": {
      exit(p) {
        // `for (x in o)` / `for (x of i)` may come from `for (var x in o)`.
        // Restoring `var` is exact only when x already is a `var` of this
        // same function (a redeclaration); an outer/closure x must stay as is.
        if (!t.isIdentifier(p.node.left)) return;
        const b = p.scope.getBinding(p.node.left.name);
        const fnScope = p.scope.getFunctionParent() || p.scope.getProgramParent();
        if (!b || b.kind !== "var" || b.scope !== fnScope) return;
        p.node.left = t.variableDeclaration("var", [
          t.variableDeclarator(t.identifier(p.node.left.name)),
        ]);
      },
    },
  });
});

/* ================================================================== *
 * 4y. `var f = function f() {}` back to `function f() {}` (CFF turns   *
 *     functions it can't flatten into this, at the top of their block). *
 *     Exact when the names match (self-references keep meaning the     *
 *     same function), it is the variable's only write, and only inert  *
 *     statements precede it in its block (nothing can observe the      *
 *     earlier hoisting).                                               *
 * ================================================================== */
const inertExpr = (e) =>
  !e ||
  (t.isLiteral(e) && !t.isTemplateLiteral(e)) ||
  t.isFunctionExpression(e) ||
  t.isArrowFunctionExpression(e) ||
  t.isIdentifier(e, { name: "undefined" }) ||
  (t.isUnaryExpression(e) && ["-", "+", "!", "void"].includes(e.operator) && t.isLiteral(e.argument)) ||
  (t.isArrayExpression(e) && e.elements.every((x) => x === null || inertExpr(x))) ||
  (t.isObjectExpression(e) && e.properties.every((pp) => t.isObjectProperty(pp) && !pp.computed && inertExpr(pp.value)));
const inertStmt = (st) =>
  t.isFunctionDeclaration(st) ||
  (t.isVariableDeclaration(st) && st.kind === "var" && st.declarations.every((x) => t.isIdentifier(x.id) && inertExpr(x.init))) ||
  (t.isExpressionStatement(st) && t.isAssignmentExpression(st.expression, { operator: "=" }) && t.isIdentifier(st.expression.left) && inertExpr(st.expression.right));
pass("functionExpressionsToDeclarations", (ast, ctx) => {
  recrawl(ast);
  let converted = 0;
  traverse(ast, {
    VariableDeclaration(path) {
      const node = path.node;
      if (node.kind !== "var" || node.declarations.length !== 1) return;
      const d = node.declarations[0];
      if (!t.isIdentifier(d.id) || !t.isFunctionExpression(d.init)) return;
      const fe = d.init;
      if (fe.id && fe.id.name !== d.id.name) {
        // a differing self-name is fine if the body never uses it
        const own = path.get("declarations.0.init").scope.getOwnBinding(fe.id.name);
        if (own && own.kind === "local" && own.referencePaths.length) return;
        if (own && own.kind !== "local") {
          // shadowed by a body declaration: the self-name is unreachable
        }
      }
      if (!(path.parentPath.isProgram() || (path.parentPath.isBlockStatement() && path.parentPath.parentPath.isFunction()))) return;
      const b = path.scope.getBinding(d.id.name);
      if (!b || b.path.node !== d || b.constantViolations.length) return;
      const list = path.container;
      for (let i = 0; i < path.key; i++) if (!inertStmt(list[i])) return;
      path.replaceWith(t.functionDeclaration(t.identifier(d.id.name), fe.params, fe.body, fe.generator, fe.async));
      converted++;
    },
  });
  ctx.stats.functionExpressions = { converted };
});

/* ================================================================== *
 * 4z. drop `var x;` made redundant by `function x() {}` in the same    *
 *     function body (the declaration already creates and initialises  *
 *     the binding). Earlier reversals can leave such pairs, and they   *
 *     make the name resolve to the var instead of the function.        *
 * ================================================================== */
pass("dropRedundantVars", (ast, ctx) => {
  recrawl(ast);
  let dropped = 0;
  traverse(ast, {
    FunctionDeclaration(path) {
      const parent = path.parentPath;
      // only declarations directly in a function body / the program
      if (!(parent.isProgram() || (parent.isBlockStatement() && parent.parentPath.isFunction()))) return;
      const b = parent.scope.getBinding(path.node.id.name);
      if (!b || !b.path.isVariableDeclarator() || b.path.node.init) return;
      const owner = (p) => p.getFunctionParent() || p.scope.getProgramParent().path;
      if (owner(b.path) !== owner(path)) return;
      const decl = b.path.parentPath;
      if (decl.parentPath.isForXStatement() || decl.parentPath.isForStatement()) return;
      if (decl.node.declarations.length === 1) decl.remove();
      else b.path.remove();
      dropped++;
    },
  });
  ctx.stats.redundantVars = { dropped };
});

/* ================================================================== *
 * 4a. un-lazy function declarations (MovedDeclarations on PREDICTABLE  *
 *     functions): `function g() {}` inside F became a packed param of F *
 *     plus `if (!g) { g = function () {} }` at the top of F's body.    *
 *     When no caller ever passes that param and that is its only       *
 *     write, g is undefined on entry, so the declaration is exact.     *
 *     The unused param itself is dropped later (unParameterPacking).   *
 * ================================================================== */
pass("unLazyFunctions", (ast, ctx) => {
  let converted = 0;
  for (let round = 0; round < 10; round++) {
    recrawl(ast);
    let changed = false;
    traverse(ast, {
      Function(fp) {
        const fn = fp.node;
        if (!t.isBlockStatement(fn.body)) return;
        // F's own binding: declaration, or a lazily bound param itself
        let fBinding = null;
        if (fp.isFunctionDeclaration() && fn.id) fBinding = fp.parentPath.scope.getBinding(fn.id.name);
        else if (
          fp.parentPath.isAssignmentExpression({ operator: "=" }) &&
          t.isIdentifier(fp.parentPath.node.left) &&
          fp.parentPath.parentPath.isExpressionStatement()
        )
          fBinding = fp.parentPath.scope.getBinding(fp.parentPath.node.left.name);
        // property of a local object only ever called as O[k]() / O[k].apply(thisArg)
        // (the dispatcher's fns object): its functions never receive arguments
        let zeroArgObject = false;
        if (!fBinding && fp.parentPath.isObjectProperty() && fp.key === "value") {
          const objPath = fp.parentPath.parentPath;
          let ob = null;
          if (objPath.parentPath.isVariableDeclarator() && objPath.key === "init" && t.isIdentifier(objPath.parent.id))
            ob = objPath.parentPath.scope.getBinding(objPath.parent.id.name);
          else if (objPath.parentPath.isAssignmentExpression({ operator: "=" }) && objPath.key === "right" && t.isIdentifier(objPath.parent.left))
            ob = objPath.parentPath.scope.getBinding(objPath.parent.left.name);
          if (ob && ob.constantViolations.length <= 1 && ob.referencePaths.length > 0) {
            zeroArgObject = ob.referencePaths.every((rp) => {
              const mem = rp.parentPath;
              if (!mem.isMemberExpression() || rp.key !== "object") return false;
              const up = mem.parentPath;
              if (up.isCallExpression() && mem.key === "callee") return up.node.arguments.length === 0;
              if (up.isMemberExpression() && mem.key === "object" && memberPropString(up.node) === "apply") {
                const call = up.parentPath;
                return call.isCallExpression() && up.key === "callee" && call.node.arguments.length <= 1;
              }
              return false;
            });
          }
        }
        // highest arg count any caller passes (only direct calls allowed)
        let maxArgs = 0;
        let callersKnown = true;
        for (const rp of fBinding ? fBinding.referencePaths : []) {
          const call = rp.parentPath;
          if (call.isUnaryExpression({ operator: "!" })) continue; // the lazy `if (!F)` test
          // `new F(a)` passes arguments exactly like `F(a)`
          if (!(call.isCallExpression() || call.isNewExpression()) || rp.key !== "callee") {
            callersKnown = false;
            break;
          }
          if (call.node.arguments.some((a) => !t.isExpression(a))) {
            callersKnown = false;
            break;
          }
          maxArgs = Math.max(maxArgs, call.node.arguments.length);
        }
        const body = fn.body.body;
        for (let i = 0; i < body.length; i++) {
          const st = body[i];
          if (t.isVariableDeclaration(st) && st.declarations.every((d) => !d.init)) continue;
          if (
            !t.isIfStatement(st) ||
            st.alternate ||
            !t.isUnaryExpression(st.test, { operator: "!" }) ||
            !t.isIdentifier(st.test.argument) ||
            !t.isBlockStatement(st.consequent) ||
            st.consequent.body.length !== 1 ||
            !t.isExpressionStatement(st.consequent.body[0]) ||
            !t.isAssignmentExpression(st.consequent.body[0].expression, { operator: "=" }) ||
            !t.isIdentifier(st.consequent.body[0].expression.left, { name: st.test.argument.name }) ||
            !t.isFunctionExpression(st.consequent.body[0].expression.right) ||
            st.consequent.body[0].expression.right.id
          )
            break; // only the leading run of lazy inits
          const name = st.test.argument.name;
          const b = fp.scope.getOwnBinding(name);
          if (!b || b.constantViolations.length !== 1) continue;
          let dropVar = null;
          if (b.kind === "param") {
            // a packed param no caller ever passes
            if (!((fBinding && callersKnown) || zeroArgObject)) continue;
            const idx = fn.params.findIndex((p) => t.isIdentifier(p, { name }));
            if (idx < 0 || idx < maxArgs) continue;
          } else if (b.kind === "var") {
            // a bare `var g;` of this function: undefined on entry
            if (!b.path.isVariableDeclarator() || b.path.node.init || b.path.getFunctionParent() !== fp) continue;
            const declStmt = b.path.parentPath;
            if (!declStmt.parentPath.isBlockStatement() || declStmt.parentPath.parent !== fn) continue;
            dropVar = b.path;
          } else continue;
          const fe = st.consequent.body[0].expression.right;
          body[i] = t.functionDeclaration(t.identifier(name), fe.params, fe.body, fe.generator, fe.async);
          if (dropVar) {
            const decl = dropVar.parent;
            decl.declarations.splice(decl.declarations.indexOf(dropVar.node), 1);
            if (!decl.declarations.length) body.splice(body.indexOf(decl), 1), i--;
          }
          converted++;
          changed = true;
        }
      },
    });
    if (!changed) break;
  }
  ctx.stats.lazyFunctions = { converted };
});

/* ================================================================== *
 * 4b. un-ControlFlowFlattening (MEDIUM+) — see lib/cff.mjs             *
 * ================================================================== */
pass("unControlFlowFlattening", (ast, ctx) => {
  reverseControlFlowFlattening(ast, ctx);
});

/* ================================================================== *
 * 5. un-DuplicateLiteralsRemoval:  `const A = [<simples>]` + A[n]      *
 * ================================================================== */
pass("unDuplicateLiteralsRemoval", (ast, ctx) => {
  /*
   * `var A = [0x0, 0x1, "length", …]` with every use a read A[<index>].
   * Exact for an array that is never reassigned and never written through
   * (every reference is a non-assignment A[integer literal in range]).
   * All qualifying arrays are handled, resolved by binding (names repeat).
   */
  recrawl(ast);
  let replaced = 0;
  const arrays = [];
  traverse(ast, {
    VariableDeclarator(path) {
      const d = path.node;
      if (!t.isIdentifier(d.id)) return;
      const binding = path.scope.getBinding(d.id.name);
      if (!binding || binding.path.node !== d) return;
      // `var A = [...]`, or `var A; … A = [...]` (CFF reconstruction) when only
      // declarations precede the assignment, so every read happens after it
      let arr = d.init;
      let assignStmt = null;
      if (arr) {
        if (binding.constantViolations.length) return;
      } else {
        if (binding.constantViolations.length !== 1) return;
        const cv = binding.constantViolations[0];
        if (!cv.isAssignmentExpression({ operator: "=" }) || !cv.parentPath.isExpressionStatement()) return;
        const stmt = cv.parentPath;
        if (!Array.isArray(stmt.container) || stmt.container !== path.parentPath.container) return;
        for (let i = 0; i < stmt.key; i++) {
          const prev = stmt.container[i];
          // nothing before it may execute code that could read the array:
          // declarations, or `x = function () {…}` (defining runs no body)
          // inert: evaluating it runs no code (literals, functions, arrays/objects of those)
          const inert = (e) =>
            !e ||
            t.isLiteral(e) && !t.isTemplateLiteral(e) ||
            t.isFunctionExpression(e) ||
            t.isArrowFunctionExpression(e) ||
            t.isIdentifier(e, { name: "undefined" }) ||
            (t.isUnaryExpression(e) && ["-", "+", "!", "void"].includes(e.operator) && t.isLiteral(e.argument)) ||
            (t.isArrayExpression(e) && e.elements.every((x) => x === null || inert(x))) ||
            (t.isObjectExpression(e) && e.properties.every((pp) => t.isObjectProperty(pp) && !pp.computed && inert(pp.value)));
          const ok =
            t.isFunctionDeclaration(prev) ||
            (t.isVariableDeclaration(prev) && prev.declarations.every((x) => t.isIdentifier(x.id) && inert(x.init))) ||
            (t.isExpressionStatement(prev) &&
              t.isAssignmentExpression(prev.expression, { operator: "=" }) &&
              t.isIdentifier(prev.expression.left) &&
              inert(prev.expression.right));
          if (!ok) return;
        }
        arr = cv.node.right;
        assignStmt = stmt;
      }
      if (!t.isArrayExpression(arr) || arr.elements.length === 0) return;
      const vals = [];
      for (const el of arr.elements) {
        const sv = el === null ? null : simpleValueOf(el);
        if (sv === null) return;
        vals.push(sv);
      }
      const sites = [];
      let keep = false; // reads with a not-yet-literal index stay (array kept)
      for (const rp of binding.referencePaths) {
        const mp = rp.parentPath;
        if (!mp.isMemberExpression() || rp.key !== "object" || !mp.node.computed) return;
        // reads only
        if (
          (mp.parentPath.isAssignmentExpression() && mp.key === "left") ||
          mp.parentPath.isUpdateExpression() ||
          (mp.parentPath.isUnaryExpression({ operator: "delete" })) ||
          (mp.parentPath.isForXStatement() && mp.key === "left") ||
          (mp.parentPath.isCallExpression() && mp.key === "callee")
        )
          return;
        const idx = numValue(mp.node.property);
        if (idx === null) {
          keep = true;
          continue;
        }
        if (!Number.isInteger(idx) || idx < 0 || idx >= vals.length) return;
        sites.push({ mp, idx });
      }
      if (!sites.length) return;
      arrays.push({ path, vals, sites, assignStmt, keep });
    },
  });
  const names = [];
  for (const a of arrays) {
    for (const { mp, idx } of a.sites) {
      mp.replaceWith(valueNode(a.vals[idx]));
      replaced++;
    }
    names.push(a.path.node.id.name);
    if (a.keep) continue;
    if (a.assignStmt) a.assignStmt.remove();
    const decl = a.path.parentPath;
    if (decl.node.declarations.length === 1) decl.remove();
    else a.path.remove();
  }
  ctx.stats.duplicateLiteralsRemoval = { replaced, array: names.join(",") };
});

/* ================================================================== *
 * 5b. un-VariableMasking (MEDIUM): function f(a, b) { var x; … }      *
 *     became function f(...m) { m["length"] = 2; … m[0] … m[-57] … }.  *
 *     Keys 0..N-1 are the parameters, every other key a local. Exact   *
 *     when `m` is only ever used as m[<literal>] (incl. in closures)   *
 *     and the function doesn't use `arguments` (rest vs simple params  *
 *     map `arguments` differently).                                    *
 * ================================================================== */
pass("unVariableMasking", (ast, ctx) => {
  recrawl(ast);
  const used = new Set();
  traverse(ast, {
    Identifier(p) {
      used.add(p.node.name);
    },
  });
  const fresh = (base) => {
    let n = base;
    for (let i = 2; used.has(n); i++) n = `${base}${i}`;
    used.add(n);
    return n;
  };
  let functions = 0;
  traverse(ast, {
    Function: {
      exit(fp) {
        const fn = fp.node;
        if (fn.params.length !== 1 || !t.isRestElement(fn.params[0]) || !t.isIdentifier(fn.params[0].argument)) return;
        if (!t.isBlockStatement(fn.body) || fn.async || fn.generator) return;
        if ((t.isObjectMethod(fn) || t.isClassMethod(fn)) && fn.kind !== "method") return;
        const stack = fn.params[0].argument.name;
        const binding = fp.scope.getOwnBinding(stack);
        if (!binding || binding.constantViolations.length) return;

        // optional m["length"] = N — first statement, possibly after bare
        // `var x;` / function declarations (they execute nothing)
        let N = null;
        const first = fn.body.body.find(
          (st) =>
            !(t.isVariableDeclaration(st) && st.declarations.every((d) => d.init === null)) && !t.isFunctionDeclaration(st),
        );
        let lengthStmt = null;
        if (
          t.isExpressionStatement(first) &&
          t.isAssignmentExpression(first.expression, { operator: "=" }) &&
          t.isMemberExpression(first.expression.left) &&
          t.isIdentifier(first.expression.left.object, { name: stack }) &&
          memberPropString(first.expression.left) === "length" &&
          t.isNumericLiteral(first.expression.right) &&
          Number.isInteger(first.expression.right.value)
        ) {
          N = first.expression.right.value;
          lengthStmt = first;
        }

        // every use must be m[<literal>] (the length statement excepted)
        const keyOf = (m) => {
          if (!m.computed && t.isIdentifier(m.property)) return m.property.name;
          if (t.isStringLiteral(m.property)) return m.property.value;
          const v = numValue(m.property);
          return v === null ? null : String(v);
        };
        const sites = [];
        for (const rp of binding.referencePaths) {
          const mp = rp.parentPath;
          if (lengthStmt && mp.node === lengthStmt.expression.left) continue;
          if (!mp.isMemberExpression() || rp.key !== "object") return;
          const key = keyOf(mp.node);
          if (key === null || key === "length" || key === "__proto__") return;
          sites.push({ mp, key });
        }
        // own `arguments`
        let usesArguments = false;
        fp.traverse({
          Identifier(ip) {
            if (ip.node.name !== "arguments" || ip.scope.getBinding("arguments")) return;
            let f = ip.getFunctionParent();
            while (f && f.isArrowFunctionExpression()) f = f.parentPath.getFunctionParent();
            if (f === fp) usesArguments = true;
          },
        });
        if (usesArguments) return;

        const isIndex = (k) => /^(0|[1-9]\d*)$/.test(k);
        // without the length statement (PREDICTABLE functions) every
        // non-negative index becomes a parameter: callers pass exactly the
        // original arity, so the extra ones start undefined like a var.
        let paramCount = N;
        if (paramCount === null) {
          paramCount = 0;
          for (const { key } of sites) if (isIndex(key)) paramCount = Math.max(paramCount, Number(key) + 1);
        }
        const names = new Map();
        const nameFor = (k) => {
          if (!names.has(k)) names.set(k, fresh(isIndex(k) && Number(k) < paramCount ? `p${k}` : t.isValidIdentifier(k) ? `v_${k}` : `v${k.replace(/[^\w$]/g, "_")}`));
          return names.get(k);
        };
        const params = [];
        for (let i = 0; i < paramCount; i++) params.push(t.identifier(nameFor(String(i))));
        for (const { mp, key } of sites) mp.replaceWith(t.identifier(nameFor(key)));
        const locals = [...names.entries()].filter(([k]) => !(isIndex(k) && Number(k) < paramCount)).map(([, n]) => n);
        fn.params = params;
        if (lengthStmt) fn.body.body.splice(fn.body.body.indexOf(lengthStmt), 1);
        fn.body.body.unshift(...locals.map((n) => t.variableDeclaration("var", [t.variableDeclarator(t.identifier(n))])));
        functions++;
      },
    },
  });
  ctx.stats.variableMasking = { functions };
});

/* ================================================================== *
 * 6. un-StringConcealing                                              *
 * ================================================================== */
pass("unStringConcealing", (ast, ctx) => {
  /*
   * Shape (js-confuser stringConcealing):
   *   ARRAY = "<big encoded string>"
   *   function DECODER(s) { var TABLE = "<91 chars>"; ... * 91 ... 8191 ... }
   *   function GETTER(start, len) { return DECODER(ARRAY.slice(start, start + len)); }
   *   GETTER(<num>, <num>)  at every concealed string
   * GETTER / DECODER may instead be lazily bound, `if (!X) { X = function … }`,
   * to a var or an injected parameter. Every identifier is resolved through
   * its scope binding: the renamer reuses short names across scopes, so a
   * name lookup can pair a getter with another scope's decoder table.
   */
  recrawl(ast);

  const isBigObscureStr = (s) =>
    typeof s === "string" && s.length >= 100 && /^[\x21-\x7e]+$/.test(s);
  const onlyMemberObjectRefs = (b) =>
    b.referencePaths.length > 0 &&
    b.referencePaths.every(
      (rp) => rp.parentPath && rp.parentPath.isMemberExpression() && rp.parentPath.node.object === rp.node,
    );

  /*
   * Two storage layouts exist across js-confuser versions:
   *  (A) one big encoded string, getter `(start, len) => DEC(S.slice(start, start + len))`
   *  (B) an array of encoded strings + a `{}` cache, getter
   *      `function G(i) { if (typeof C[i] === "undefined") { return C[i] = DEC(A[i]); } return C[i]; }`
   */
  /* ---- candidate stores: binding -> { value | values, site } ---------- */
  const arrays = new Map(); // (A) big string, or (B) array of strings
  const caches = new Map(); // (B) `{}` cache objects
  const isStringList = (n) =>
    t.isArrayExpression(n) && n.elements.length > 0 && n.elements.every((e) => t.isStringLiteral(e));
  const isEmptyObject = (n) => t.isObjectExpression(n) && n.properties.length === 0;
  function addStore(b, init, site) {
    if (!onlyMemberObjectRefs(b)) return;
    if (t.isStringLiteral(init) && isBigObscureStr(init.value)) arrays.set(b, { value: init.value, site });
    else if (isStringList(init)) arrays.set(b, { values: init.elements.map((e) => e.value), site });
    else if (isEmptyObject(init)) caches.set(b, { site });
  }
  traverse(ast, {
    VariableDeclarator(path) {
      const { id, init } = path.node;
      if (!t.isIdentifier(id) || !init) return;
      const b = path.scope.getBinding(id.name);
      if (!b || b.path.node !== path.node || b.constantViolations.length !== 0) return;
      addStore(b, init, path.parentPath);
    },
    AssignmentExpression(path) {
      const { operator, left, right } = path.node;
      if (operator !== "=" || !t.isIdentifier(left)) return;
      if (!t.isStringLiteral(right) && !t.isArrayExpression(right) && !t.isObjectExpression(right)) return;
      const b = path.scope.getBinding(left.name);
      if (!b || b.constantViolations.length !== 1 || b.constantViolations[0].node !== path.node)
        return;
      if (b.path.isVariableDeclarator() && b.path.node.init) return;
      addStore(b, right, path.parentPath.isExpressionStatement() ? path.parentPath : path);
    },
  });
  let hasDecoder = false;
  traverse(ast, {
    Function(p) {
      if (!hasDecoder && isBase91DecoderNode(p.node)) hasDecoder = true;
    },
  });
  const unrecognized = () =>
    hasDecoder &&
    ctx.errors.push(
      "stringConcealing: a base91 string decoder is present but no string store/getter matched a known layout; strings left encoded",
    );
  if (arrays.size === 0) return void unrecognized();

  /* ---- (B) cached getter shape ---------------------------------------- */
  function isCachedGetterShape(node) {
    if (!node.params || node.params.length !== 1 || !t.isIdentifier(node.params[0])) return false;
    const i = node.params[0].name;
    if (!t.isBlockStatement(node.body) || node.body.body.length !== 2) return false;
    const [ifs, ret] = node.body.body;
    const isCi = (m, c) =>
      t.isMemberExpression(m, { computed: true }) &&
      t.isIdentifier(m.object) &&
      (c === undefined || m.object.name === c) &&
      t.isIdentifier(m.property, { name: i });
    if (!t.isIfStatement(ifs) || ifs.alternate) return false;
    const test = ifs.test;
    if (
      !t.isBinaryExpression(test, { operator: "===" }) ||
      !t.isUnaryExpression(test.left, { operator: "typeof" }) ||
      !isCi(test.left.argument) ||
      !t.isStringLiteral(test.right, { value: "undefined" })
    )
      return false;
    const c = test.left.argument.object.name;
    const inner = singleStatement(ifs.consequent);
    if (!t.isReturnStatement(inner) || !t.isAssignmentExpression(inner.argument, { operator: "=" }))
      return false;
    const asg = inner.argument;
    if (!isCi(asg.left, c)) return false;
    const call = asg.right;
    if (!t.isCallExpression(call) || !t.isIdentifier(call.callee) || call.arguments.length !== 1)
      return false;
    if (!isCi(call.arguments[0]) || call.arguments[0].object.name === c) return false;
    return t.isReturnStatement(ret) && isCi(ret.argument, c);
  }

  /* ---- getter shape: (start, len) => DECODER(ARRAY.slice(start, start + len)) */
  function isGetterShape(node) {
    if (!node.params || node.params.length !== 2) return false;
    const [p0, p1] = node.params;
    if (!t.isIdentifier(p0) || !t.isIdentifier(p1)) return false;
    if (!t.isBlockStatement(node.body) || node.body.body.length !== 1) return false;
    const ret = node.body.body[0];
    if (!t.isReturnStatement(ret) || !t.isCallExpression(ret.argument)) return false;
    const outer = ret.argument;
    if (!t.isIdentifier(outer.callee) || outer.arguments.length !== 1) return false;
    const sliceCall = outer.arguments[0];
    if (!t.isCallExpression(sliceCall) || sliceCall.arguments.length !== 2) return false;
    if (memberPropString(sliceCall.callee) !== "slice") return false;
    if (!t.isIdentifier(sliceCall.callee.object)) return false;
    if (!t.isIdentifier(sliceCall.arguments[0], { name: p0.name })) return false;
    const a2 = sliceCall.arguments[1];
    return (
      t.isIdentifier(a2, { name: p1.name }) ||
      (t.isBinaryExpression(a2, { operator: "+" }) &&
        t.isIdentifier(a2.left, { name: p0.name }) &&
        t.isIdentifier(a2.right, { name: p1.name }))
    );
  }
  // `slice(start, len)` vs `slice(start, start + len)` both slice [start, start+len)
  // only when the 2nd arg is start+len; plain `len` is slice(start, len).
  function sliceEnd(node, start, length) {
    const a2 = node.body.body[0].argument.arguments[0].arguments[1];
    return t.isBinaryExpression(a2) ? start + length : length;
  }

  /* ---- base91 decoder shape ---------------------------------------- */
  /** visit the nodes of a function body, excluding nested functions */
  function ownNodes(fn, visit) {
    walkNodes(fn.body, (n, parents) => {
      if (!parents.some((p) => t.isFunction(p))) visit(n);
    });
  }
  function isBase91FnNode(fn) {
    if (!fn || !t.isFunction(fn) || !t.isBlockStatement(fn.body)) return false;
    let has91 = false,
      has8191 = false,
      hasTable = false;
    ownNodes(fn, (n) => {
      if (t.isBinaryExpression(n, { operator: "*" }) && t.isNumericLiteral(n.right, { value: 91 }))
        has91 = true;
      else if (t.isNumericLiteral(n, { value: 8191 })) has8191 = true;
      else if (
        (t.isVariableDeclarator(n) && t.isStringLiteral(n.init) && t.isIdentifier(n.id)) ||
        (t.isAssignmentExpression(n, { operator: "=" }) && t.isIdentifier(n.left) && t.isStringLiteral(n.right))
      )
        hasTable = true;
    });
    return has91 && has8191 && hasTable;
  }

  /** the decoder's table: the string-initialized local used with `.indexOf` */
  function tableOfFn(fn) {
    // a local written exactly once with a string (declarator or `x = "…"`)
    const candidates = new Map();
    const writes = new Map();
    const bump = (name) => writes.set(name, (writes.get(name) || 0) + 1);
    ownNodes(fn, (n) => {
      if (t.isVariableDeclarator(n) && t.isIdentifier(n.id) && n.init) {
        bump(n.id.name);
        if (t.isStringLiteral(n.init)) candidates.set(n.id.name, n.init.value);
      } else if (t.isAssignmentExpression(n) && t.isIdentifier(n.left)) {
        bump(n.left.name);
        if (n.operator === "=" && t.isStringLiteral(n.right)) candidates.set(n.left.name, n.right.value);
      } else if (t.isUpdateExpression(n) && t.isIdentifier(n.argument)) bump(n.argument.name);
    });
    for (const name of [...candidates.keys()]) if (writes.get(name) !== 1) candidates.delete(name);
    let table = null;
    let count = 0;
    ownNodes(fn, (n) => {
      if (
        t.isMemberExpression(n) &&
        t.isIdentifier(n.object) &&
        candidates.has(n.object.name) &&
        memberPropString(n) === "indexOf"
      ) {
        const v = candidates.get(n.object.name);
        if (v !== table) count++;
        table = v;
      }
    });
    return count === 1 && table.length === 91 ? table : null;
  }

  /* ---- lazy wrappers: if (!X) { X = function … }  keyed by binding ---- */
  const lazyByBinding = new Map(); // binding -> {path, kind, fnPath, assign} | null (ambiguous)
  const lazyWrappers = [];
  traverse(ast, {
    IfStatement(path) {
      const node = path.node;
      if (node.alternate || !t.isUnaryExpression(node.test, { operator: "!" })) return;
      if (!t.isIdentifier(node.test.argument)) return;
      const nm = node.test.argument.name;
      if (!t.isBlockStatement(node.consequent) || node.consequent.body.length !== 1) return;
      const st = node.consequent.body[0];
      if (!t.isExpressionStatement(st)) return;
      const ex = st.expression;
      if (
        !t.isAssignmentExpression(ex, { operator: "=" }) ||
        !t.isIdentifier(ex.left, { name: nm }) ||
        !t.isFunctionExpression(ex.right)
      )
        return;
      const kind = isGetterShape(ex.right)
        ? "getter"
        : isCachedGetterShape(ex.right)
          ? "cgetter"
          : isBase91FnNode(ex.right)
            ? "decoder"
            : null;
      if (!kind) return;
      const b = path.scope.getBinding(nm);
      if (!b) return;
      const lw = { path, kind, fnPath: path.get("consequent.body.0.expression.right"), assign: ex };
      lazyWrappers.push(lw);
      lazyByBinding.set(b, lazyByBinding.has(b) ? null : lw);
    },
  });
  const lazyOf = (b, kind) => {
    const lw = lazyByBinding.get(b);
    if (!lw || lw.kind !== kind) return null;
    // the lazy assignment must be the binding's only write
    if (!b.constantViolations.every((cv) => cv.node === lw.assign)) return null;
    return lw;
  };

  const declGetters = new Map(); // node -> FunctionDeclaration path
  traverse(ast, {
    FunctionDeclaration(path) {
      if (!path.node.id) return;
      if (isGetterShape(path.node)) declGetters.set(path.node, { path, kind: "getter" });
      else if (isCachedGetterShape(path.node)) declGetters.set(path.node, { path, kind: "cgetter" });
    },
  });

  /** the single function declaration that defines `b` — also when it shares
   *  a name with a param (the declaration replaces the param on entry, and
   *  babel lists it as a write of the param binding) */
  function fnDeclOf(b) {
    if (b.path.isFunctionDeclaration()) return writesOf(b).length === 0 ? b.path : null;
    if (b.kind !== "param") return null;
    const decls = b.constantViolations.filter((cv) => cv.isFunctionDeclaration());
    return decls.length === 1 && b.constantViolations.length === 1 ? decls[0] : null;
  }
  /** getter binding -> getter function path (of the given layout kind) */
  function getterFnPath(b, kind = "getter") {
    const dp = fnDeclOf(b);
    if (dp) {
      const g = declGetters.get(dp.node);
      return g && g.kind === kind ? dp : null;
    }
    if (b.path.isFunctionDeclaration()) return null;
    return lazyOf(b, kind)?.fnPath ?? null;
  }
  /** decoder binding -> decoder function node */
  function decoderFn(b) {
    const dp = fnDeclOf(b);
    if (dp) return isBase91FnNode(dp.node) ? dp.node : null;
    if (b.path.isFunctionDeclaration()) return null;
    return lazyOf(b, "decoder")?.fnPath.node ?? null;
  }

  /* ---- resolve every call site -------------------------------------- */
  const replacements = [];
  const failures = [];
  const usedArrays = new Set();
  const usedCaches = new Set();
  const cacheSlots = new Map(); // cache binding -> Map(index -> decoded)

  /** decode one value with the decoder bound at `decId` */
  function decodeWith(decId, encoded, where) {
    const db = decId.scope.getBinding(decId.node.name);
    const dec = db ? decoderFn(db) : null;
    if (!dec) return failures.push({ where, reason: "decoder not resolved" }), null;
    const table = tableOfFn(dec);
    if (table === null) return failures.push({ where, reason: "decoder table not found" }), null;
    let decoded;
    try {
      decoded = base91Decode(table, encoded);
    } catch {
      decoded = null;
    }
    if (typeof decoded !== "string") return failures.push({ where, reason: "decode error" }), null;
    return decoded;
  }

  /** layout (B): G(i) with a cached getter */
  function resolveCached(path) {
    const node = path.node;
    const a0 = node.arguments[0];
    if (!t.isNumericLiteral(a0) || !Number.isInteger(a0.value) || a0.value < 0) return;
    const gb = path.scope.getBinding(node.callee.name);
    if (!gb) return;
    const fp = getterFnPath(gb, "cgetter");
    if (!fp) return;
    const index = a0.value;
    const ifs = fp.get("body.body.0");
    const asg = ifs.get("consequent").isBlockStatement()
      ? ifs.get("consequent.body").find((p) => p.isReturnStatement()).get("argument")
      : ifs.get("consequent.argument");
    const cacheId = asg.get("left.object");
    const decCall = asg.get("right");
    const arrId = decCall.get("arguments.0.object");
    const ab = arrId.scope.getBinding(arrId.node.name);
    const arr = ab ? arrays.get(ab) : null;
    const cb = cacheId.scope.getBinding(cacheId.node.name);
    const cache = cb ? caches.get(cb) : null;
    if (!arr || !arr.values) return failures.push({ where: index, reason: "string array not resolved" });
    if (!cache) return failures.push({ where: index, reason: "cache object not resolved" });
    if (cache.private === undefined) {
      // the cache must only be touched inside cached getters
      cache.private = cb.referencePaths.every((rp) => {
        const f = rp.getFunctionParent();
        if (!f) return false;
        const fnNode = f.node;
        if (declGetters.get(fnNode)?.kind === "cgetter") return true;
        return lazyWrappers.some((lw) => lw.kind === "cgetter" && lw.fnPath.node === fnNode);
      });
    }
    if (!cache.private) return failures.push({ where: index, reason: "cache used outside getters" });
    if (index >= arr.values.length) return failures.push({ where: index, reason: "index out of range" });
    const decoded = decodeWith(decCall.get("callee"), arr.values[index], index);
    if (decoded === null) return;
    // getters with different decoders share one cache: the first call wins at
    // runtime, so every getter must agree on the value of a shared index
    if (!cacheSlots.has(cb)) cacheSlots.set(cb, new Map());
    const slots = cacheSlots.get(cb);
    if (slots.has(index) && slots.get(index) !== decoded)
      return failures.push({ where: index, reason: "cache index decoded inconsistently" });
    slots.set(index, decoded);
    usedArrays.add(arr);
    usedCaches.add(cache);
    replacements.push({ path, decoded });
  }

  traverse(ast, {
    CallExpression(path) {
      const node = path.node;
      if (t.isIdentifier(node.callee) && node.arguments.length === 1) return resolveCached(path);
      if (!t.isIdentifier(node.callee) || node.arguments.length !== 2) return;
      const [a0, a1] = node.arguments;
      if (!t.isNumericLiteral(a0) || !t.isNumericLiteral(a1)) return;
      const start = a0.value;
      const length = a1.value;
      if (!Number.isInteger(start) || !Number.isInteger(length) || start < 0 || length < 0) return;

      const gb = path.scope.getBinding(node.callee.name);
      if (!gb) return;
      const fp = getterFnPath(gb);
      if (!fp) return;

      const ret = fp.get("body.body.0.argument");
      const decId = ret.get("callee");
      const arrId = ret.get("arguments.0.callee.object");
      const db = decId.scope.getBinding(decId.node.name);
      const ab = arrId.scope.getBinding(arrId.node.name);
      const arr = ab ? arrays.get(ab) : null;
      if (!arr || arr.value === undefined) {
        failures.push({ start, reason: "string array not resolved" });
        return;
      }
      const dec = db ? decoderFn(db) : null;
      if (!dec) {
        failures.push({ start, reason: "decoder not resolved" });
        return;
      }
      const table = tableOfFn(dec);
      if (table === null) {
        failures.push({ start, reason: "decoder table not found" });
        return;
      }
      const encoded = arr.value.slice(start, sliceEnd(fp.node, start, length));
      let decoded;
      try {
        decoded = base91Decode(table, encoded);
      } catch {
        failures.push({ start, reason: "decode error" });
        return;
      }
      if (typeof decoded !== "string") {
        failures.push({ start, reason: "decoded non-string" });
        return;
      }
      usedArrays.add(arr);
      replacements.push({ path, decoded });
    },
  });

  const stringsOut = [];
  for (const r of replacements) {
    r.path.replaceWith(t.stringLiteral(r.decoded));
    r.path.skip();
    stringsOut.push(r.decoded);
  }
  ctx.stats.stringConcealing = {
    strings: [...new Set(stringsOut)],
    replaced: replacements.length,
    failed: failures.length,
  };
  if (replacements.length === 0 && failures.length === 0) return void unrecognized();
  if (failures.length > 0) {
    ctx.errors.push(
      `stringConcealing: ${failures.length} unresolved (${[...new Set(failures.map((f) => f.reason))].join(", ")})`,
    );
    return;
  }

  /* ---- cleanup: remove only machinery nothing else still uses -------- */
  // A store or getter we didn't recognise (e.g. a Variable-Masked getter)
  // may still reference the same array; removing it would break the code.
  const candidateNodes = new Set([
    ...declGetters.keys(),
    ...lazyWrappers.map((lw) => lw.path.node),
    ...[...usedArrays].map((a) => a.site.node),
    ...[...usedCaches].map((c) => c.site.node),
  ]);
  recrawl(ast);
  const cand = []; // { path, binding }
  traverse(ast, {
    "FunctionDeclaration|IfStatement|VariableDeclaration|ExpressionStatement|AssignmentExpression"(path) {
      if (!candidateNodes.has(path.node)) return;
      const n = path.node;
      let name = null;
      let scope = path.scope;
      if (t.isFunctionDeclaration(n)) {
        name = n.id.name;
        scope = path.parentPath.scope;
      } else if (t.isIfStatement(n)) name = n.test.argument.name;
      else if (t.isVariableDeclaration(n)) name = n.declarations[0].id.name;
      else if (t.isExpressionStatement(n)) name = n.expression.left?.name;
      else if (t.isAssignmentExpression(n)) name = n.left.name;
      const binding = name ? scope.getBinding(name) : null;
      if (binding) cand.push({ path, binding });
    },
  });
  let keep = new Set(cand);
  for (let changed = true; changed; ) {
    changed = false;
    const live = [...keep];
    for (const c of live) {
      const uses = [...c.binding.referencePaths, ...writesOf(c.binding)];
      const ok = uses.every((u) => live.some((o) => u === o.path || u.isDescendant(o.path)));
      if (!ok) {
        keep.delete(c);
        changed = true;
      }
    }
  }
  for (const c of keep) if (!c.path.removed) c.path.remove();
  if (keep.size < cand.length)
    ctx.errors.push(
      `stringConcealing: ${cand.length - keep.size} machinery item(s) kept because unrecognised code still uses them`,
    );
  // leftover `var X;` bare-zero refs are GC'd in a later pass
});

/* ================================================================== *
 * 6b. un-StringConcealing machinery (getGlobal / bufferToString chain) *
 *      Transitive taint closure from the root machinery functions:     *
 *      any top-level statement whose value references machinery is     *
 *      machinery, and its assignment targets become machinery too.     *
 * ================================================================== */
pass("unMachinery", (ast, ctx) => {
  /*
   * After all strings are recovered, the decoders and their support code
   * (getGlobal, bufferToString, the TextDecoder/Buffer/utf8 setup globals) are
   * dead. Everything is resolved through scope bindings, and nothing is
   * removed unless every reference to it lies inside other removed machinery.
   */
  const sc = ctx.stats.stringConcealing;
  // never while concealed strings remain; otherwise safe: only machinery that
  // nothing else uses is removed (also leftovers exposed in later rounds)
  if (sc && sc.failed !== 0) return;
  let removed = 0;

  // 1. decoder copies nothing references any more (anywhere in the tree)
  for (let changed = true, guard = 0; changed && guard < 50; guard++) {
    changed = false;
    recrawl(ast);
    traverse(ast, {
      FunctionDeclaration(path) {
        if (!path.node.id || !isBase91DecoderNode(path.node)) return;
        const b = fnDeclBinding(path);
        if (!b || b.referencePaths.length) return;
        path.remove();
        removed++;
        changed = true;
      },
    });
  }

  // 2. machinery closure at program level
  recrawl(ast);
  let programPath = null;
  traverse(ast, {
    Program(p) {
      programPath = p;
      p.stop();
    },
  });
  const pscope = programPath.scope;
  const bodyPaths = programPath.get("body");

  const roots = new Map(); // binding -> stmt path
  for (const sp of bodyPaths) {
    // `function f() {}`, `var f = function () {}` or `f = function () {}` (CFF rebuild)
    let st = sp.node;
    let name = null;
    let fnNode = null;
    if (t.isFunctionDeclaration(st) && st.id) {
      name = st.id.name;
      fnNode = st;
    } else if (t.isVariableDeclaration(st) && st.declarations.length === 1 && t.isIdentifier(st.declarations[0].id) && t.isFunctionExpression(st.declarations[0].init)) {
      name = st.declarations[0].id.name;
      fnNode = st.declarations[0].init;
    } else if (t.isExpressionStatement(st) && t.isAssignmentExpression(st.expression, { operator: "=" }) && t.isIdentifier(st.expression.left) && t.isFunctionExpression(st.expression.right)) {
      name = st.expression.left.name;
      fnNode = st.expression.right;
    }
    if (!fnNode) continue;
    st = fnNode;
    const code = nodeCode(st);
    const isGetGlobal =
      st.params.length === 0 &&
      code.includes("globalThis") &&
      code.includes("window") &&
      code.includes('"return this"');
    const isBufferToString =
      st.params.length === 1 && code.includes(".decode(") && code.includes(".from(") && code.includes("utf-8");
    if (!isGetGlobal && !isBufferToString) continue;
    const b = pscope.getOwnBinding(name);
    if (!b) continue;
    // its only definition must be this statement
    const defs = [b.path.node, ...b.constantViolations.map((cv) => cv.node)];
    const own = t.isFunctionDeclaration(sp.node) ? b.path.node === sp.node && !b.constantViolations.length
      : t.isVariableDeclaration(sp.node) ? b.path.node === sp.node.declarations[0] && !b.constantViolations.length
      : b.constantViolations.length === 1 && b.constantViolations[0].node === sp.node.expression && !(b.path.isVariableDeclarator() && b.path.node.init);
    if (own) roots.set(b, sp);
    void defs;
  }
  if (roots.size === 0) {
    ctx.stats.machinery = { removed, bindings: 0 };
    return;
  }

  /** program-scope binding written by a top-level `X = …;` / `var X = …;` */
  function targetOf(sp) {
    if (sp.isExpressionStatement() && sp.get("expression").isAssignmentExpression({ operator: "=" })) {
      const left = sp.node.expression.left;
      if (!t.isIdentifier(left)) return null;
      const b = pscope.getOwnBinding(left.name);
      return b ? { binding: b, value: sp.get("expression.right") } : null;
    }
    if (sp.isVariableDeclaration() && sp.node.declarations.length === 1) {
      const d = sp.get("declarations.0");
      if (!t.isIdentifier(d.node.id) || !d.node.init) return null;
      const b = pscope.getOwnBinding(d.node.id.name);
      return b ? { binding: b, value: d.get("init") } : null;
    }
    return null;
  }
  /** bindings referenced inside `p` that are declared outside `p` */
  function freeRefs(p) {
    const out = new Set();
    let opaque = false;
    p.traverse({
      ReferencedIdentifier(ip) {
        const b = ip.scope.getBinding(ip.node.name);
        if (!b) return; // global (Object, String, globalThis, …)
        if (b.path.isDescendant(p) || b.path === p) return; // local to p
        out.add(b);
      },
      ThisExpression(tp) {
        if (!tp.getFunctionParent()) opaque = true; // top-level `this`
      },
    });
    return opaque ? null : out;
  }

  const machinery = new Map(roots); // binding -> defining stmt path
  for (let changed = true; changed; ) {
    changed = false;
    for (const sp of bodyPaths) {
      const tg = targetOf(sp);
      if (!tg || machinery.has(tg.binding)) continue;
      const refs = freeRefs(tg.value);
      if (!refs || refs.size === 0) continue;
      if (![...refs].every((b) => machinery.has(b))) continue;
      // the target must be written only here (plus a bare `var X;`)
      if (writesOf(tg.binding).some((cv) => cv.node !== sp.node.expression)) continue;
      machinery.set(tg.binding, sp);
      changed = true;
    }
  }

  // 3. shrink: keep only machinery whose every use is inside removed machinery
  const inside = (p, set) => [...set].some((sp) => p === sp || p.isDescendant(sp));
  for (let changed = true; changed; ) {
    changed = false;
    const stmts = new Set(machinery.values());
    for (const [b, sp] of machinery) {
      const uses = [...b.referencePaths, ...writesOf(b).filter((cv) => cv.node !== sp.node.expression)];
      if (uses.every((u) => inside(u, stmts))) continue;
      machinery.delete(b);
      changed = true;
    }
  }

  const stmts = new Set(machinery.values());
  for (const sp of stmts) {
    sp.remove();
    removed++;
  }
  ctx.stats.machinery = { removed, bindings: machinery.size };
});

/* ================================================================== *
 * 7. un-Calculator                                                    *
 * ================================================================== */
pass("unCalculator", (ast, ctx) => {
  let calcName = null;
  let calcPath = null;
  const opMap = new Map();
  traverse(ast, {
    FunctionDeclaration(path) {
      if (calcName) return;
      const node = path.node;
      if (node.params.length !== 3) return;
      const [o, a, b] = node.params;
      if (!t.isIdentifier(o) || !t.isIdentifier(a) || !t.isIdentifier(b)) return;
      if (!t.isBlockStatement(node.body) || node.body.body.length !== 1) return;
      const sw = node.body.body[0];
      if (!t.isSwitchStatement(sw)) return;
      if (!t.isIdentifier(sw.discriminant, { name: o.name })) return;
      if (sw.cases.length === 0) return;
      const ops = new Map();
      for (const cs of sw.cases) {
        if (!cs.test || !t.isStringLiteral(cs.test)) return;
        if (cs.consequent.length !== 1) return;
        const ret = cs.consequent[0];
        if (!t.isReturnStatement(ret) || !ret.argument) return;
        if (!t.isBinaryExpression(ret.argument)) return;
        const bin = ret.argument;
        if (
          !t.isIdentifier(bin.left, { name: a.name }) ||
          !t.isIdentifier(bin.right, { name: b.name })
        )
          return;
        ops.set(cs.test.value, bin.operator);
      }
      calcName = node.id.name;
      ops.forEach((v, k) => opMap.set(k, v));
      calcPath = path;
      path.stop();
    },
  });
  if (!calcName) return;

  let replaced = 0;
  traverse(ast, {
    CallExpression: {
      exit(path) {
        const node = path.node;
        if (!t.isIdentifier(node.callee, { name: calcName })) return;
        if (node.arguments.length !== 3) return;
        const [k, a, b] = node.arguments;
        if (!t.isStringLiteral(k)) return;
        const op = opMap.get(k.value);
        if (!op) return;
        if (t.isSpreadElement(a) || t.isSpreadElement(b)) return;
        path.replaceWith(t.binaryExpression(op, a, b));
        path.skip();
        replaced++;
      },
    },
  });

  // still referenced? -> keep; else remove declaration
  let remaining = false;
  traverse(ast, {
    ReferencedIdentifier(p) {
      if (p.node.name === calcName) remaining = true;
    },
  });
  if (!remaining && calcPath.node) calcPath.remove();
  ctx.stats.calculator = { replaced };
});
/* ================================================================== *
 * 7b. un-StringSplitting (MEDIUM): "hello world" became               *
 *     ("hel" + "lo w") + "orld". Folding is exact: "a" + "b" === "ab", *
 *     and (x + "a") + "b" === x + "ab" since x + "a" is already a      *
 *     string (x is converted to a primitive once either way).          *
 * ================================================================== */
pass("unStringSplitting", (ast, ctx) => {
  let folded = 0;
  traverse(ast, {
    BinaryExpression: {
      exit(path) {
        const n = path.node;
        if (n.operator !== "+" || !t.isStringLiteral(n.right)) return;
        if (t.isStringLiteral(n.left)) {
          path.replaceWith(t.stringLiteral(n.left.value + n.right.value));
          folded++;
        } else if (t.isBinaryExpression(n.left, { operator: "+" }) && t.isStringLiteral(n.left.right)) {
          path.replaceWith(
            t.binaryExpression("+", n.left.left, t.stringLiteral(n.left.right.value + n.right.value)),
          );
          folded++;
        }
      },
    },
  });
  ctx.stats.stringSplitting = { folded };
});


/* ================================================================== *
 * 7c. un-GlobalConcealing (MEDIUM): `console` became MAP("k") with     *
 *     function MAP(m) { switch (m) { case "k": return G["console"]; … } }*
 *     where G = getGlobal(). Each literal call becomes the global's     *
 *     name — the original source form — when nothing at the call site *
 *     shadows that name. (Via G an undeclared global reads undefined   *
 *     instead of throwing; the original code, restored here, threw.)   *
 * ================================================================== */
pass("unGlobalConcealing", (ast, ctx) => {
  recrawl(ast);
  let replaced = 0;
  const maps = []; // { binding, table: Map(key -> name), globalBinding }
  traverse(ast, {
    FunctionDeclaration(path) {
      const fn = path.node;
      if (!fn.id || fn.params.length !== 1 || !t.isIdentifier(fn.params[0])) return;
      // a lone switch (bare `var x;` declarations execute nothing)
      const rest = fn.body.body.filter((st) => !(t.isVariableDeclaration(st) && st.declarations.every((d) => d.init === null)));
      if (rest.length !== 1 || !t.isSwitchStatement(rest[0])) return;
      const sw = rest[0];
      if (!t.isIdentifier(sw.discriminant, { name: fn.params[0].name })) return;
      if (sw.cases.length < 3) return;
      let gName = null;
      const table = new Map();
      for (const c of sw.cases) {
        if (!t.isStringLiteral(c.test) || c.consequent.length !== 1 || !t.isReturnStatement(c.consequent[0])) return;
        const arg = c.consequent[0].argument;
        if (!t.isMemberExpression(arg) || !t.isIdentifier(arg.object)) return;
        const name = memberPropString(arg);
        if (name === null) return;
        if (gName === null) gName = arg.object.name;
        else if (gName !== arg.object.name) return;
        if (!table.has(c.test.value)) table.set(c.test.value, name);
      }
      // G must be the getGlobal() result, never written elsewhere
      // `var G = getGlobal();` — or `var G; … G = getGlobal();` (Moved Declarations)
      const gb = path.scope.getBinding(gName);
      if (!gb || !gb.path.isVariableDeclarator()) return;
      let init = gb.path.node.init;
      if (init && gb.constantViolations.length) return;
      if (!init) {
        if (gb.constantViolations.length !== 1) return;
        const cv = gb.constantViolations[0];
        if (!cv.isAssignmentExpression({ operator: "=" }) || !cv.parentPath.isExpressionStatement()) return;
        init = cv.node.right;
      }
      if (!t.isCallExpression(init) || !t.isIdentifier(init.callee) || init.arguments.length) return;
      // getGlobal: a function declaration, or a var written once with a function expression
      const getGlobal = gb.path.scope.getBinding(init.callee.name);
      if (!getGlobal) return;
      let ggFn = null;
      if (getGlobal.path.isFunctionDeclaration()) ggFn = getGlobal.path.node;
      else if (getGlobal.path.isVariableDeclarator()) {
        const w = [...(getGlobal.path.node.init ? [getGlobal.path.node.init] : []), ...getGlobal.constantViolations.map((cv) => (cv.isAssignmentExpression({ operator: "=" }) ? cv.node.right : null))];
        if (w.length === 1 && t.isFunctionExpression(w[0])) ggFn = w[0];
      }
      if (!ggFn) return;
      const code = nodeCode(ggFn);
      if (!(code.includes("globalThis") && code.includes("window") && code.includes('"return this"'))) return;
      maps.push({ binding: path.parentPath.scope.getBinding(fn.id.name), table, fnNode: fn });
    },
  });
  for (const m of maps) {
    if (!m.binding || m.binding.path.node !== m.fnNode || m.binding.constantViolations.length) continue;
    for (const rp of m.binding.referencePaths) {
      const call = rp.parentPath;
      if (!call.isCallExpression() || rp.key !== "callee" || call.node.arguments.length !== 1) continue;
      const a = call.node.arguments[0];
      if (!t.isStringLiteral(a) || !m.table.has(a.value)) continue;
      const name = m.table.get(a.value);
      if (!t.isValidIdentifier(name) || call.scope.getBinding(name)) continue;
      // an assignment/update target can't take a plain call; never produced, skip anyway
      if (call.parentPath.isAssignmentExpression() && call.key === "left") continue;
      call.replaceWith(t.identifier(name));
      replaced++;
    }
  }
  ctx.stats.globalConcealing = { replaced };
});

/* ================================================================== *
 * 7d. un-OpaquePredicates (HIGH): `test` became `!("k" in DUMMY) &&    *
 *     test`; `return x` became `if (!("k" in DUMMY)) { return x } else *
 *     { return "fake" }`. DUMMY is an empty, never-written function    *
 *     whose only uses are `"<string>" in DUMMY`, so each test is        *
 *     folded to its value for a plain function object (false for any   *
 *     name not on Function.prototype), then constant logic is folded.   *
 * ================================================================== */
const PLAIN_FUNCTION = function () {};
pass("unOpaquePredicates", (ast, ctx) => {
  recrawl(ast);
  let folded = 0;
  // DUMMY candidates
  const dummies = new Set();
  traverse(ast, {
    FunctionDeclaration(path) {
      const fn = path.node;
      if (fn.params.length || fn.body.body.length || fn.async || fn.generator) return;
      const b = fnDeclBinding(path);
      if (!b || !b.referencePaths.length) return;
      const ok = b.referencePaths.every(
        (rp) => rp.parentPath.isBinaryExpression({ operator: "in" }) && rp.key === "right" && t.isStringLiteral(rp.parent.left),
      );
      if (ok) dummies.add(b);
    },
  });
  if (!dummies.size) return;
  for (const b of dummies)
    for (const rp of b.referencePaths) {
      const bin = rp.parentPath;
      bin.replaceWith(t.booleanLiteral(bin.node.left.value in PLAIN_FUNCTION));
      folded++;
    }
  // fold the constant logic the predicates sit in
  const truthy = (n) => (t.isBooleanLiteral(n) ? n.value : null);
  traverse(ast, {
    UnaryExpression: {
      exit(p) {
        if (p.node.operator === "!" && t.isBooleanLiteral(p.node.argument)) p.replaceWith(t.booleanLiteral(!p.node.argument.value));
      },
    },
    LogicalExpression: {
      exit(p) {
        const l = truthy(p.node.left);
        if (l === null) return;
        // true && x -> x ; false && x -> false ; true || x -> true ; false || x -> x
        if (p.node.operator === "&&") p.replaceWith(l ? p.node.right : p.node.left);
        else if (p.node.operator === "||") p.replaceWith(l ? p.node.left : p.node.right);
      },
    },
    ConditionalExpression: {
      exit(p) {
        const c = truthy(p.node.test);
        if (c !== null) p.replaceWith(c ? p.node.consequent : p.node.alternate);
      },
    },
    IfStatement: {
      exit(p) {
        const c = truthy(p.node.test);
        if (c === null) return;
        const branch = c ? p.node.consequent : p.node.alternate;
        if (!branch) return void p.remove();
        // inline a block only when it declares nothing block-scoped
        if (t.isBlockStatement(branch)) {
          const scoped = branch.body.some(
            (st) => t.isFunctionDeclaration(st) || t.isClassDeclaration(st) || (t.isVariableDeclaration(st) && st.kind !== "var"),
          );
          if (!scoped && (p.parentPath.isBlockStatement() || p.parentPath.isProgram() || p.parentPath.isSwitchCase())) {
            if (branch.body.length) p.replaceWithMultiple(branch.body);
            else p.remove();
            return;
          }
        }
        p.replaceWith(branch);
      },
    },
  });
  ctx.stats.opaquePredicates = { folded };
});

/* ================================================================== *
 * 9c. write-only locals: a function-local `var x` that is never read  *
 *     and only ever assigned literals (CFF's leftover `didReturn`      *
 *     flag: `return (x = true, v)`) — the writes and the var go.       *
 *     Exact: nothing can observe a variable nobody reads.              *
 * ================================================================== */
pass("dropWriteOnlyLocals", (ast, ctx) => {
  recrawl(ast);
  let dropped = 0;
  traverse(ast, {
    VariableDeclarator(path) {
      if (!t.isIdentifier(path.node.id) || path.node.init) return;
      if (!path.parentPath.parentPath.isBlockStatement() || !path.parentPath.parentPath.parentPath.isFunction()) return;
      const b = path.scope.getBinding(path.node.id.name);
      if (!b || b.path !== path || b.kind !== "var" || b.referencePaths.length) return;
      const writes = b.constantViolations;
      if (!writes.length) return;
      // each write: `x = <literal>` as a statement, or the first item of a sequence
      const plan = [];
      for (const w of writes) {
        if (!w.isAssignmentExpression({ operator: "=" }) || !t.isLiteral(w.node.right) || t.isTemplateLiteral(w.node.right)) return;
        if (w.parentPath.isExpressionStatement()) plan.push({ kind: "stmt", w });
        else if (w.parentPath.isSequenceExpression() && w.key === 0) plan.push({ kind: "seq", w });
        else return;
      }
      for (const { kind, w } of plan) {
        if (kind === "stmt") w.parentPath.remove();
        else {
          const seq = w.parentPath;
          const rest = seq.node.expressions.slice(1);
          seq.replaceWith(rest.length === 1 ? rest[0] : t.sequenceExpression(rest));
        }
      }
      const decl = path.parentPath;
      if (decl.node.declarations.length === 1) decl.remove();
      else path.remove();
      dropped++;
    },
  });
  ctx.stats.writeOnlyLocals = { dropped };
});

/* ================================================================== *
 * 7e. un-Flatten (HIGH): a function's body moved to                    *
 *     function F_flat(O, [a, b]) { … O["k"] … } at program level and   *
 *     the function became function f(...args) { var O = { get "k"() {  *
 *     return x }, set "k"(v) { x = v }, get "t"() { return typeof y },  *
 *     "c"(...a) { return g(...a) } }; return F_flat(O, args); }.        *
 *     The body is put back into f with its params; O["k"] -> x,         *
 *     O["t"] -> typeof y, O["c"](…) -> g(…). Exact when F_flat is only *
 *     called from f, O is only read as O[<key>], and the body uses no  *
 *     this/arguments (Flatten skips those functions).                  *
 * ================================================================== */
pass("unFlatten", (ast, ctx) => {
  let restored = 0;
  for (let round = 0; round < 50; round++) {
    recrawl(ast);
    let did = false;
    traverse(ast, {
      Function(fp) {
        if (did) return;
        const fn = fp.node;
        if (fn.params.length !== 1 || !t.isRestElement(fn.params[0]) || !t.isIdentifier(fn.params[0].argument)) return;
        if (!t.isBlockStatement(fn.body)) return; // (...a) => expr
        const argsName = fn.params[0].argument.name;
        const body = fn.body.body;
        if (body.length !== 2) return;
        const [decl, ret] = body;
        if (!t.isVariableDeclaration(decl) || decl.declarations.length !== 1 || !t.isIdentifier(decl.declarations[0].id)) return;
        const objName = decl.declarations[0].id.name;
        const obj = decl.declarations[0].init;
        if (!t.isObjectExpression(obj)) return;
        if (
          !t.isReturnStatement(ret) ||
          !t.isCallExpression(ret.argument) ||
          !t.isIdentifier(ret.argument.callee) ||
          ret.argument.arguments.length !== 2 ||
          !t.isIdentifier(ret.argument.arguments[0], { name: objName }) ||
          !t.isIdentifier(ret.argument.arguments[1], { name: argsName })
        )
          return;
        // the mapping object
        const map = new Map(); // key -> { get, set, typeofOf, call }
        const keyOf = (p) => (t.isStringLiteral(p.key) ? p.key.value : t.isIdentifier(p.key) && !p.computed ? p.key.name : null);
        for (const p of obj.properties) {
          if (!t.isObjectMethod(p)) return;
          const k = keyOf(p);
          if (k === null || p.body.body.length !== 1) return;
          const st = p.body.body[0];
          const e = map.get(k) || {};
          if (p.kind === "get" && t.isReturnStatement(st) && t.isIdentifier(st.argument)) e.get = st.argument.name;
          else if (p.kind === "get" && t.isReturnStatement(st) && t.isUnaryExpression(st.argument, { operator: "typeof" }) && t.isIdentifier(st.argument.argument))
            e.typeofOf = st.argument.argument.name;
          else if (
            p.kind === "set" && p.params.length === 1 && t.isIdentifier(p.params[0]) && t.isExpressionStatement(st) &&
            t.isAssignmentExpression(st.expression, { operator: "=" }) && t.isIdentifier(st.expression.left) &&
            t.isIdentifier(st.expression.right, { name: p.params[0].name })
          )
            e.set = st.expression.left.name;
          else if (
            p.kind === "method" && p.params.length === 1 && t.isRestElement(p.params[0]) && t.isReturnStatement(st) &&
            t.isCallExpression(st.argument) && t.isIdentifier(st.argument.callee) && st.argument.arguments.length === 1 &&
            t.isSpreadElement(st.argument.arguments[0]) && t.isIdentifier(st.argument.arguments[0].argument, { name: p.params[0].argument.name })
          )
            e.call = st.argument.callee.name;
          else return;
          map.set(k, e);
        }
        for (const e of map.values()) if (e.set && e.get && e.set !== e.get) return;
        // F_flat: a declaration, or `f = [async] function (…) {}` as the only
        // write of `f` with only inert statements before it (so it is defined
        // before any call can happen)
        const flatB = fp.scope.getBinding(ret.argument.callee.name);
        if (!flatB || flatB.referencePaths.length !== 1) return;
        let flatPath = null;
        let flatStmt = null;
        if (flatB.path.isFunctionDeclaration()) {
          if (writesOf(flatB).length) return;
          flatPath = flatB.path;
          flatStmt = flatB.path;
        } else if (flatB.path.isVariableDeclarator() && !flatB.path.node.init && flatB.constantViolations.length === 1) {
          const cv = flatB.constantViolations[0];
          if (!cv.isAssignmentExpression({ operator: "=" }) || !cv.parentPath.isExpressionStatement()) return;
          const stmt = cv.parentPath;
          if (!Array.isArray(stmt.container)) return;
          for (let i = 0; i < stmt.key; i++) if (!inertStmt(stmt.container[i])) return;
          const right = cv.get("right");
          if (!right.isFunctionExpression()) return;
          flatPath = right;
          flatStmt = stmt;
        } else return;
        const flat = flatPath.node;
        if (flat.generator) return;
        if (flat.async !== fn.async) return;
        // param forms: (O, [a, b])  — or strict: () { "use strict"; var [O, [a, b]] = arguments; … }
        let strictForm = false;
        if (flat.params.length === 0 && flat.body.directives?.some((dd) => dd.value.value === "use strict")) {
          const first = flat.body.body[0];
          if (
            !t.isVariableDeclaration(first) || first.declarations.length !== 1 ||
            !t.isArrayPattern(first.declarations[0].id) || first.declarations[0].id.elements.length !== 2 ||
            !t.isIdentifier(first.declarations[0].id.elements[0]) || !t.isArrayPattern(first.declarations[0].id.elements[1]) ||
            !t.isIdentifier(first.declarations[0].init, { name: "arguments" })
          )
            return;
          // restoring needs an already-strict context (class code): "use strict"
          // with non-simple params would be a syntax error
          if (!fp.findParent((x) => x.isClass())) return;
          strictForm = true;
          if (flat.body.directives.some((dd) => dd.value.value !== "use strict")) return;
        } else if (flat.body.directives?.length) return;
        // O and the param pattern (not modified until every check passed)
        const oId = strictForm ? flat.body.body[0].declarations[0].id.elements[0] : flat.params[0];
        const pattern = strictForm ? flat.body.body[0].declarations[0].id.elements[1] : flat.params[1];
        if (!strictForm && (flat.params.length !== 2 || !t.isIdentifier(flat.params[0]) || !t.isArrayPattern(flat.params[1]))) return;
        if (pattern.elements.some((e) => e === null)) return;
        const O = oId.name;
        const ob = flatPath.scope.getOwnBinding(O);
        if (!ob || ob.constantViolations.length) return;
        // strict form: `arguments` is consumed by the unpack only
        if (strictForm) {
          const argsB = [];
          flatPath.traverse({
            Identifier(ip) {
              if (ip.node.name === "arguments" && !ip.scope.getBinding("arguments") && ip.node !== flat.body.body[0].declarations[0].init) {
                let f = ip.getFunctionParent();
                while (f && f.isArrowFunctionExpression()) f = f.parentPath.getFunctionParent();
                if (f === flatPath) argsB.push(ip);
              }
            },
          });
          if (argsB.length) return;
        }
        // every use of O: O[<key>] in a supported position
        const sites = [];
        for (const rp of ob.referencePaths) {
          const mp = rp.parentPath;
          if (!mp.isMemberExpression() || rp.key !== "object") return;
          const k = memberPropString(mp.node);
          const e = k === null ? null : map.get(k);
          if (!e) return;
          const isCallee = mp.parentPath.isCallExpression() && mp.key === "callee";
          const isWrite =
            (mp.parentPath.isAssignmentExpression() && mp.key === "left") || mp.parentPath.isUpdateExpression() ||
            (mp.parentPath.isForXStatement() && mp.key === "left");
          if (mp.parentPath.isUnaryExpression({ operator: "delete" })) return;
          let name;
          if (e.call) {
            if (!isCallee) return;
            name = e.call;
          } else if (e.typeofOf) {
            if (isWrite || isCallee) return;
            name = e.typeofOf;
          } else {
            if (isCallee) return; // calls go through a call mapping
            if (isWrite && !e.set) {
              // getter-only: non-strict code silently drops the write (a
              // JS-Confuser bug that changes behaviour) — keep it dropped by
              // writing to a fresh unused local; compound writes are declined
              const plain = (mp.parentPath.isAssignmentExpression({ operator: "=" }) && mp.key === "left") || (mp.parentPath.isForXStatement() && mp.key === "left");
              if (!plain) return;
              sites.push({ mp, e, name: null, sink: true });
              continue;
            }
            if (!(mp.parentPath.isAssignmentExpression({ operator: "=" }) && mp.key === "left") && !e.get) return;
            name = e.get || e.set;
          }
          sites.push({ mp, e, name });
        }
        // own this / arguments in the body would change meaning (the strict
        // unpack's own `arguments` is accounted for above)
        let unsafe = false;
        flatPath.traverse({
          ThisExpression(tp) {
            let f = tp.getFunctionParent();
            while (f && f.isArrowFunctionExpression()) f = f.parentPath.getFunctionParent();
            if (f === flatPath) unsafe = true;
          },
          Identifier(ip) {
            if (ip.node.name !== "arguments" || ip.scope.getBinding("arguments")) return;
            if (strictForm && ip.node === flat.body.body[0].declarations[0].init) return;
            let f = ip.getFunctionParent();
            while (f && f.isArrowFunctionExpression()) f = f.parentPath.getFunctionParent();
            if (f === flatPath) unsafe = true;
          },
        });
        if (unsafe) return;
        // the restored names must mean, at each site, what they meant in f:
        // rename any local of F_flat that would shadow them
        const restoredNames = new Set(sites.filter((x) => x.name).map((x) => x.name));
        flatPath.traverse({
          Scopable(sp) {
            for (const nm of Object.keys(sp.scope.bindings)) if (restoredNames.has(nm)) sp.scope.rename(nm, sp.scope.generateUid(nm));
          },
        });
        for (const nm of Object.keys(flatPath.scope.bindings)) if (restoredNames.has(nm)) flatPath.scope.rename(nm, flatPath.scope.generateUid(nm));
        // and from f's position they must resolve as the getters did
        for (const nm of restoredNames) {
          const fromF = fp.scope.getBinding(nm);
          const inObj = fp.get("body.body.0.declarations.0.init").scope.getBinding(nm);
          if (fromF !== inObj) return;
        }
        let sinkName = null;
        for (const { mp, e, name, sink } of sites) {
          if (sink) {
            sinkName = sinkName || flatPath.scope.generateUid("ignoredWrite");
            mp.replaceWith(t.identifier(sinkName));
          } else mp.replaceWith(e.typeofOf ? t.unaryExpression("typeof", t.identifier(name)) : t.identifier(name));
        }
        // put the body back
        if (strictForm) {
          flat.body.body.shift(); // the `var [O, [...]] = arguments` unpack
          flat.body.directives = []; // class code is strict already
        }
        fn.params = pattern.elements;
        fn.body = flat.body;
        if (sinkName) fn.body.body.unshift(t.variableDeclaration("var", [t.variableDeclarator(t.identifier(sinkName))]));
        flatStmt.remove();
        restored++;
        did = true;
        fp.stop();
      },
    });
    if (!did) break;
  }
  ctx.stats.flatten = { restored };
});

/* ================================================================== *
 * 8. un-DeadCode:  if ("prop" in FN) { FN(); }                        *
 * ================================================================== */
pass("unDeadCode", (ast, ctx) => {
  /*
   * js-confuser deadCode, per block:
   *   if ("<random>" in DUMMY) { DEAD() }   function DEAD() { <template junk> }
   * DUMMY is one empty program-level `function DUMMY() {}`; "<random>" was
   * verified at obfuscation time not to be a property of functions, so the
   * predicate is always false. MovedDeclarations may later turn DEAD into a
   * lazily bound param: `if (!DEAD) { DEAD = function () {...} }`.
   */
  recrawl(ast);
  let removed = 0;
  traverse(ast, {
    IfStatement(path) {
      const node = path.node;
      const test = node.test;
      if (
        node.alternate ||
        !t.isBinaryExpression(test, { operator: "in" }) ||
        !t.isStringLiteral(test.left) ||
        !t.isIdentifier(test.right)
      )
        return;
      const only = t.isBlockStatement(node.consequent)
        ? node.consequent.body.length === 1 ? node.consequent.body[0] : null
        : node.consequent;
      if (
        !t.isExpressionStatement(only) ||
        !t.isCallExpression(only.expression) ||
        !t.isIdentifier(only.expression.callee) ||
        only.expression.arguments.length !== 0
      )
        return;

      // DUMMY: empty, never-written FunctionDeclaration
      const dummy = path.scope.getBinding(test.right.name);
      if (
        !dummy ||
        !dummy.path.isFunctionDeclaration() ||
        dummy.path.node.params.length !== 0 ||
        dummy.path.node.body.body.length !== 0 ||
        writesOf(dummy).length !== 0
      )
        return;

      // The guard never runs, so it goes regardless. DEAD itself goes too
      // when its only uses are that call and its own lazy init.
      const deadDef = deadDefinition(path.scope.getBinding(only.expression.callee.name), only.expression.callee, dummy);
      path.remove();
      removed++;
      if (deadDef) deadDef.remove();
    },
  });
  ctx.stats.deadCode = { removed };

  /** the removable definition of DEAD (decl or lazy `if (!D) {D = fn}`), or null */
  function deadDefinition(dead, callee, dummy) {
    if (!dead || dead === dummy) return null;
    const name = callee.name;
    let def = null;
    if (dead.path.isFunctionDeclaration()) {
      if (writesOf(dead).length !== 0) return null;
      def = dead.path;
    } else {
      const writes = writesOf(dead);
      if (writes.length === 0) {
        // lazy init already gone: nothing left to remove
      } else if (writes.length === 1) {
        const w = writes[0];
        const ifPath = w.parentPath?.parentPath?.parentPath;
        if (
          !w.isAssignmentExpression({ operator: "=" }) ||
          !t.isFunctionExpression(w.node.right) ||
          !ifPath ||
          !ifPath.isIfStatement() ||
          ifPath.node.alternate ||
          !t.isUnaryExpression(ifPath.node.test, { operator: "!" }) ||
          !t.isIdentifier(ifPath.node.test.argument, { name }) ||
          ifPath.node.consequent.body?.length !== 1
        )
          return null;
        def = ifPath;
      } else return null;
    }
    const lazyTest = def && def.isIfStatement() ? def.node.test.argument : null;
    for (const rp of dead.referencePaths)
      if (rp.node !== callee && rp.node !== lazyTest) return null;
    return def;
  }
});

/* ================================================================== *
 * 9. un-Dispatcher                                                    *
 * ================================================================== */
pass("unDispatcher", (ast, ctx) => {
  /*
   * Template (js-confuser dispatcher.ts), per block:
   *   function DISP(name, flag, ret, fnLengths = {...}, ...mdParams) {
   *     var output; var fns = { K: function () { var [params] = payload; body } };
   *     if (flag === CLEAR) { payload = []; }
   *     if (flag === NONCALL) { ...cache[name] || (cache[name] = createFn()) ... fns[name].apply(this) }
   *     else { output = fns[name](); }
   *     return ret === OBJ ? { OBJKEY: output } : output;   (or if/else form)
   *   }
   *   var payload; var cache = Object.create(null);
   * Call sites:
   *   f(a, b)  -> (payload = [a, b], DISP(K))       f() -> DISP(K, CLEAR)
   *   f (ref)  -> DISP(K, NONCALL)
   *   any of the above optionally: [new] DISP(K, flag|NOMEANING, OBJ)[OBJKEY]
   *
   * Rebuild (plain form): function FN(a, b) { <md locals>; body }.
   * Exact because the obfuscator only dispatches functions that do not use
   * this / arguments / eval and have no default params (so the payload
   * unpack is equivalent to binding the call arguments directly). Only
   * observable difference: `FN.length` equals the original source's
   * parameter count instead of the obfuscated wrapper's.
   */
  let found = 0;
  let unwrapped = 0;
  let restored = 0;
  const skip = new WeakSet();

  const usedNames = new Set();
  traverse(ast, {
    Identifier(p) {
      usedNames.add(p.node.name);
    },
  });
  let nameCounter = 0;
  const freshName = () => {
    let n;
    do n = `fn${nameCounter++}`;
    while (usedNames.has(n));
    usedNames.add(n);
    return n;
  };

  for (let guard = 0; guard < 1000; guard++) {
    recrawl(ast);
    let d = null;
    traverse(ast, {
      FunctionDeclaration(path) {
        if (d || skip.has(path.node)) return;
        const r = detectDispatcher(path);
        if (r) {
          d = r;
          path.stop();
        }
      },
    });
    if (!d) break;
    found++;
    const res = unwrapDispatcher(ast, d, freshName);
    if (typeof res === "number") {
      unwrapped++;
      restored += res;
    } else {
      skip.add(d.node);
      ctx.errors.push(`dispatcher ${d.node.id.name} left intact: ${res}`);
    }
  }
  if (found) ctx.stats.dispatcher = { found, unwrapped, restored };
});

function strEqTest(test, name) {
  if (!t.isBinaryExpression(test, { operator: "===" })) return null;
  if (t.isIdentifier(test.left, { name }) && t.isStringLiteral(test.right))
    return test.right.value;
  if (t.isIdentifier(test.right, { name }) && t.isStringLiteral(test.left))
    return test.left.value;
  return null;
}

function singleStatement(st) {
  // stringConcealing may inject inert decoder-copy FunctionDeclarations into blocks
  if (t.isBlockStatement(st)) {
    const rest = st.body.filter((s) => !t.isFunctionDeclaration(s));
    return rest.length === 1 ? rest[0] : null;
  }
  return st || null;
}

function singlePropObjectKey(e) {
  if (!t.isObjectExpression(e) || e.properties.length !== 1) return null;
  return simplePropKey(e.properties[0]);
}

function isUndefinedValue(e) {
  return (
    e == null ||
    t.isIdentifier(e, { name: "undefined" }) ||
    (t.isUnaryExpression(e, { operator: "void" }) && t.isNumericLiteral(e.argument))
  );
}

/** `Object.create(null)` / `Object["create"](null)` */
function isObjectCreateNull(e) {
  return (
    t.isCallExpression(e) &&
    e.arguments.length === 1 &&
    t.isNullLiteral(e.arguments[0]) &&
    t.isMemberExpression(e.callee) &&
    t.isIdentifier(e.callee.object, { name: "Object" }) &&
    memberPropString(e.callee) === "create"
  );
}

function detectDispatcher(path) {
  const node = path.node;
  if (!node.id || node.async || node.generator) return null;
  if (!(path.parentPath.isProgram() || path.parentPath.isBlockStatement()))
    return null;
  const ps = node.params;
  if (ps.length < 3) return null;
  for (let i = 0; i < 3; i++) if (!t.isIdentifier(ps[i])) return null;
  const [nameP, flagP, retP] = [ps[0].name, ps[1].name, ps[2].name];
  if (new Set([nameP, flagP, retP]).size !== 3) return null;
  const body = node.body.body;

  // fns object: `var fns = {...}` or `fns = {...}` (after md param packing)
  let fnsName = null;
  let fns = null;
  for (const st of body) {
    let id = null;
    let obj = null;
    if (
      t.isVariableDeclaration(st) &&
      st.declarations.length === 1 &&
      t.isIdentifier(st.declarations[0].id) &&
      t.isObjectExpression(st.declarations[0].init)
    ) {
      id = st.declarations[0].id.name;
      obj = st.declarations[0].init;
    } else if (
      t.isExpressionStatement(st) &&
      t.isAssignmentExpression(st.expression, { operator: "=" }) &&
      t.isIdentifier(st.expression.left) &&
      t.isObjectExpression(st.expression.right)
    ) {
      id = st.expression.left.name;
      obj = st.expression.right;
    }
    if (!obj || obj.properties.length === 0) continue;
    const m = new Map();
    let ok = true;
    for (const p of obj.properties) {
      const key = t.isObjectProperty(p) ? simplePropKey(p) : null;
      if (
        key === null ||
        m.has(key) ||
        !t.isFunctionExpression(p.value) ||
        p.value.id ||
        p.value.async ||
        p.value.generator
      ) {
        ok = false;
        break;
      }
      m.set(key, p.value);
    }
    if (!ok) continue;
    fnsName = id;
    fns = m;
    break;
  }
  if (!fns || !path.scope.getOwnBinding(fnsName)) return null;

  let clearFlag = null,
    payloadName = null,
    nonCallFlag = null,
    cacheName = null,
    objFlag = null,
    objPropKey = null;

  const isFnsNameCall = (n) =>
    t.isMemberExpression(n, { computed: true }) &&
    t.isIdentifier(n.object, { name: fnsName }) &&
    t.isIdentifier(n.property, { name: nameP });

  for (const st of body) {
    if (t.isIfStatement(st)) {
      const v = strEqTest(st.test, flagP);
      if (v !== null) {
        const only = singleStatement(st.consequent);
        if (
          !st.alternate &&
          t.isExpressionStatement(only) &&
          t.isAssignmentExpression(only.expression, { operator: "=" }) &&
          t.isIdentifier(only.expression.left) &&
          t.isArrayExpression(only.expression.right) &&
          only.expression.right.elements.length === 0
        ) {
          clearFlag = v;
          payloadName = only.expression.left.name;
          continue;
        }
        let cache = null;
        let apply = false;
        let direct = false;
        subTraverse(st.consequent, {
          LogicalExpression({ node: n }) {
            if (
              n.operator === "||" &&
              t.isMemberExpression(n.left, { computed: true }) &&
              t.isIdentifier(n.left.object) &&
              t.isIdentifier(n.left.property, { name: nameP }) &&
              t.isAssignmentExpression(n.right, { operator: "=" }) &&
              t.isMemberExpression(n.right.left, { computed: true }) &&
              t.isIdentifier(n.right.left.object, { name: n.left.object.name }) &&
              t.isIdentifier(n.right.left.property, { name: nameP })
            )
              cache = n.left.object.name;
          },
          CallExpression({ node: n }) {
            if (
              t.isMemberExpression(n.callee) &&
              memberPropString(n.callee) === "apply" &&
              isFnsNameCall(n.callee.object) &&
              n.arguments.length === 1 &&
              t.isThisExpression(n.arguments[0])
            )
              apply = true;
          },
        });
        if (st.alternate)
          subTraverse(st.alternate, {
            CallExpression({ node: n }) {
              if (n.arguments.length === 0 && isFnsNameCall(n.callee)) direct = true;
            },
          });
        if (cache && apply && direct) {
          nonCallFlag = v;
          cacheName = cache;
        }
        continue;
      }
      const r = strEqTest(st.test, retP);
      if (r !== null) {
        const only = singleStatement(st.consequent);
        const k = t.isReturnStatement(only) ? singlePropObjectKey(only.argument) : null;
        if (k !== null) {
          objFlag = r;
          objPropKey = k;
        }
      }
    } else if (t.isReturnStatement(st) && t.isConditionalExpression(st.argument)) {
      const r = strEqTest(st.argument.test, retP);
      const k = r !== null ? singlePropObjectKey(st.argument.consequent) : null;
      if (k !== null) {
        objFlag = r;
        objPropKey = k;
      }
    }
  }
  if (clearFlag === null || nonCallFlag === null || clearFlag === nonCallFlag)
    return null;
  if (payloadName === cacheName) return null;
  // payload & cache live outside the dispatcher (not shadowed inside it)
  if (path.scope.getOwnBinding(payloadName) || path.scope.getOwnBinding(cacheName))
    return null;
  const payloadBinding = path.scope.getBinding(payloadName);
  const cacheBinding = path.scope.getBinding(cacheName);
  const dispBinding = path.parentPath.scope.getBinding(node.id.name);
  if (!payloadBinding || !cacheBinding || !dispBinding) return null;
  if (dispBinding.path.node !== node) return null;

  return {
    path,
    node,
    fns,
    payloadName,
    payloadBinding,
    cacheBinding,
    dispBinding,
    clearFlag,
    nonCallFlag,
    objFlag,
    objPropKey,
  };
}

/** identifiers assigned by a destructuring target; null if any target is not a plain identifier */
function patternLeaves(p) {
  if (t.isIdentifier(p)) return [p];
  if (t.isAssignmentPattern(p)) return patternLeaves(p.left);
  if (t.isRestElement(p)) return patternLeaves(p.argument);
  if (t.isArrayPattern(p)) {
    const out = [];
    for (const e of p.elements) {
      if (e === null) continue;
      const l = patternLeaves(e);
      if (!l) return null;
      out.push(...l);
    }
    return out;
  }
  if (t.isObjectPattern(p)) {
    const out = [];
    for (const pr of p.properties) {
      const l = patternLeaves(t.isRestElement(pr) ? pr : pr.value);
      if (!l) return null;
      out.push(...l);
    }
    return out;
  }
  return null;
}

/** is `p` (an Identifier path) a variable reference/binding (not a key/label)? */
function isVariableIdentifier(p) {
  const parent = p.parent;
  if (t.isMemberExpression(parent) && parent.property === p.node && !parent.computed)
    return false;
  if (t.isOptionalMemberExpression(parent) && parent.property === p.node && !parent.computed)
    return false;
  if (
    (t.isObjectProperty(parent) || t.isObjectMethod(parent) || t.isClassMethod(parent) ||
      t.isClassProperty(parent) || t.isClassPrivateProperty(parent)) &&
    parent.key === p.node &&
    !parent.computed
  )
    return t.isObjectProperty(parent) && parent.shorthand; // shorthand {x} is a ref
  if (
    (t.isLabeledStatement(parent) || t.isBreakStatement(parent) || t.isContinueStatement(parent)) &&
    parent.label === p.node
  )
    return false;
  if (t.isMetaProperty(parent)) return false;
  return true;
}

function nonArrowFunctionParent(p) {
  let f = p.getFunctionParent();
  while (f && f.isArrowFunctionExpression()) f = f.parentPath.getFunctionParent();
  return f;
}

function isMdIf(st, mdNames) {
  return (
    t.isIfStatement(st) &&
    !st.alternate &&
    t.isUnaryExpression(st.test, { operator: "!" }) &&
    t.isIdentifier(st.test.argument) &&
    mdNames.has(st.test.argument.name) &&
    t.isBlockStatement(st.consequent) &&
    st.consequent.body.length === 1 &&
    t.isExpressionStatement(st.consequent.body[0]) &&
    t.isAssignmentExpression(st.consequent.body[0].expression, { operator: "=" }) &&
    t.isIdentifier(st.consequent.body[0].expression.left, {
      name: st.test.argument.name,
    }) &&
    t.isFunctionExpression(st.consequent.body[0].expression.right)
  );
}

/** validate one fns FunctionExpression; returns a plan or a failure string */
function planFunction(fp, d) {
  const fe = fp.node;
  const dispScope = d.path.scope;
  let bad = null;
  const payloadRefs = [];
  fp.traverse({
    Identifier(ip) {
      if (bad || !isVariableIdentifier(ip)) return;
      const name = ip.node.name;
      const b = ip.scope.getBinding(name);
      if (b && b.scope === dispScope) bad = `captures dispatcher-local ${name}`;
      else if (b && b === d.payloadBinding) {
        // writes are call-site `payload = [...]` (checked when unwrapping)
        if (!(ip.parentPath.isAssignmentExpression() && ip.key === "left")) payloadRefs.push(ip);
      }
      else if (!b && (name === "arguments" || name === "eval")) {
        if (name === "eval" || nonArrowFunctionParent(ip) === fp) bad = `uses ${name}`;
      }
    },
    ThisExpression(tp) {
      if (!bad && nonArrowFunctionParent(tp) === fp) bad = "uses this";
    },
  });
  if (bad) return bad;

  const md = [];
  for (const p of fe.params) {
    if (t.isIdentifier(p)) md.push({ name: p.name, init: null });
    else if (t.isAssignmentPattern(p) && t.isIdentifier(p.left))
      md.push({ name: p.left.name, init: p.right });
    else return "unexpected param shape";
  }
  const mdNames = new Set(md.map((m) => m.name));
  const stmts = fe.body.body;
  let i = 0;
  const mdIfs = [];
  while (i < stmts.length && isMdIf(stmts[i], mdNames)) mdIfs.push(stmts[i++]);

  let origParams = [];
  let hasUnpack = false;
  // Variable Masking reversal may leave bare `var a;` declarations ahead of
  // the unpack and turn `var [a] = payload` into `[a] = payload`
  const preUnpack = [];
  while (
    i < stmts.length &&
    ((t.isVariableDeclaration(stmts[i]) && stmts[i].declarations.every((dd) => dd.init === null && t.isIdentifier(dd.id))) ||
      t.isFunctionDeclaration(stmts[i]))
  )
    preUnpack.push(stmts[i++]);
  const st = stmts[i];
  const declUnpack =
    st &&
    t.isVariableDeclaration(st) &&
    st.declarations.length === 1 &&
    t.isArrayPattern(st.declarations[0].id) &&
    t.isIdentifier(st.declarations[0].init, { name: d.payloadName });
  const assignUnpack =
    st &&
    t.isExpressionStatement(st) &&
    t.isAssignmentExpression(st.expression, { operator: "=" }) &&
    t.isArrayPattern(st.expression.left) &&
    t.isIdentifier(st.expression.right, { name: d.payloadName }) &&
    // targets: own vars — or own params (fns functions are only ever called
    // with zero arguments, so their params start undefined like vars)
    patternLeaves(st.expression.left)?.every((id) => ["var", "param"].includes(fp.scope.getOwnBinding(id.name)?.kind));
  if (declUnpack || assignUnpack) {
    const els = declUnpack ? st.declarations[0].id.elements : st.expression.left.elements;
    const init = declUnpack ? st.declarations[0].init : st.expression.right;
    if (els.some((e, k) => e === null || (t.isRestElement(e) && k !== els.length - 1)))
      return "unpack shape";
    if (payloadRefs.length !== 1 || payloadRefs[0].node !== init)
      return "payload used beyond unpack";
    if (assignUnpack) {
      // the targets become parameters: they must not be written before the unpack
      for (const e of patternLeaves(st.expression.left)) if (fp.scope.getOwnBinding(e.name).constantViolations.some((cv) => stmts.indexOf(cv.getStatementParent()?.node) > -1 && stmts.indexOf(cv.getStatementParent().node) < i)) return "param written before unpack";
    }
    origParams = els;
    hasUnpack = true;
    i++;
  } else if (payloadRefs.length !== 0) {
    if (process.env.DISPDBG) console.error("DISPDBG", generate(fe).slice(0, 1500));
    return "payload used without unpack";
  }

  const origNames = new Set(
    Object.keys(t.getBindingIdentifiers({ type: "ArrayPattern", elements: origParams })),
  );
  // md function-hoists `if (!X) { X = function(){} }` run before the unpack;
  // X shared with an original param would be overwritten by it — not mirrored
  for (const s of mdIfs)
    if (origNames.has(s.test.argument.name)) return "md hoist / param clash";

  return { fp, md, mdIfs, origParams, origNames, startIndex: i, hasUnpack, preUnpack };
}

/** build the FunctionDeclaration (after call-site rewrites mutated the body) */
function buildFunction(plan, name) {
  const { fp, md, mdIfs, origParams, origNames, startIndex } = plan;
  const newBody = [];
  const converted = new Set();
  for (const s of mdIfs) {
    const x = s.test.argument.name;
    const fn2 = s.consequent.body[0].expression.right;
    const b = fp.scope.getOwnBinding(x);
    if (b && b.constantViolations.length === 1 && !fn2.id) {
      newBody.push(
        t.functionDeclaration(t.identifier(x), fn2.params, fn2.body, fn2.generator, fn2.async),
      );
      converted.add(x);
    }
  }
  // bare md params: plain `var x;` (unMovedDeclarations re-inlines inits)
  for (const m of md)
    if (!m.init && !origNames.has(m.name) && !converted.has(m.name))
      newBody.push(t.variableDeclaration("var", [t.variableDeclarator(t.identifier(m.name))]));
  // static-default md params: evaluated on entry -> `var x = <static>;`
  // (a default on a name the unpack rebinds is dead: unpack overwrites it)
  for (const m of md)
    if (m.init && !origNames.has(m.name) && !converted.has(m.name))
      newBody.push(
        t.variableDeclaration("var", [t.variableDeclarator(t.identifier(m.name), m.init)]),
      );
  for (const s of mdIfs) if (!converted.has(s.test.argument.name)) newBody.push(s);
  for (const v of plan.preUnpack || []) {
    if (t.isFunctionDeclaration(v)) {
      newBody.push(v);
      continue;
    }
    const keep = v.declarations.filter((dd) => !origNames.has(dd.id.name));
    if (keep.length) newBody.push(t.variableDeclaration("var", keep));
  }
  newBody.push(...fp.node.body.body.slice(startIndex));
  return t.functionDeclaration(t.identifier(name), origParams, t.blockStatement(newBody));
}

function replaceChild(parent, oldN, newN) {
  for (const k of Object.keys(parent)) {
    const v = parent[k];
    if (v === oldN) {
      parent[k] = newN;
      return true;
    }
    if (Array.isArray(v)) {
      const i = v.indexOf(oldN);
      if (i >= 0) {
        v[i] = newN;
        return true;
      }
    }
  }
  return false;
}

function isPayloadAssign(p, d) {
  return (
    p &&
    p.isAssignmentExpression({ operator: "=" }) &&
    t.isIdentifier(p.node.left, { name: d.payloadName }) &&
    p.scope.getBinding(d.payloadName) === d.payloadBinding &&
    t.isArrayExpression(p.node.right) &&
    p.node.right.elements.every((e) => e !== null)
  );
}

function classifySite(rp, d, plans) {
  const call = rp.parentPath;
  if (!(call.isCallExpression() || call.isNewExpression()) || rp.key !== "callee")
    return "dispatcher referenced outside a call";
  const args = call.node.arguments;
  if (args.length < 1 || args.length > 3 || !args.every((a) => t.isStringLiteral(a)))
    return "call-site argument shape";
  const [key, f1, f2] = args.map((a) => a.value);
  if (!plans.has(key)) return `unknown key ${key}`;
  let vp = call;
  let isObj = false;
  if (args.length === 3) {
    if (d.objFlag === null || f2 !== d.objFlag) return "unknown return flag";
    const mp = call.parentPath;
    if (!mp.isMemberExpression() || call.key !== "object" || memberPropString(mp.node) !== d.objPropKey)
      return "object-wrapped call not unwrapped by its key";
    vp = mp;
    isObj = true;
  } else if (call.isNewExpression()) return "new without object wrap";

  let kind;
  if (f1 === d.clearFlag) kind = "callNoArgs";
  else if (f1 === d.nonCallFlag) kind = "ref";
  else if (f1 === undefined || isObj) kind = "callWithPayload"; // obj: f1 = placeholder
  else return "unknown flag";

  const site = { rp, key, kind, vpNode: vp.node, vpParent: vp.parent };
  if (kind !== "callWithPayload") return site;

  const par = vp.parentPath;
  if (par.isSequenceExpression() && typeof vp.key === "number" && vp.key > 0) {
    const prev = par.get(`expressions.${vp.key - 1}`);
    if (isPayloadAssign(prev, d))
      return { ...site, mode: "seq", assignNode: prev.node, seqNode: par.node, seqParent: par.parent };
  } else if (par.isExpressionStatement() && typeof par.key === "number" && par.key > 0) {
    const prevStmt = par.getSibling(par.key - 1);
    if (prevStmt.isExpressionStatement() && isPayloadAssign(prevStmt.get("expression"), d))
      return {
        ...site,
        mode: "stmt",
        assignNode: prevStmt.node.expression,
        prevStmt: prevStmt.node,
        stmtNode: par.node,
        list: par.container,
      };
  }
  return "payload assignment not adjacent to call";
}

function removeDeclarator(binding, isRemovableInit) {
  const dp = binding.path;
  if (!dp || !dp.isVariableDeclarator() || !isRemovableInit(dp.node.init)) return;
  const decl = dp.parent;
  const list = dp.parentPath.container;
  if (!Array.isArray(list)) return;
  decl.declarations.splice(decl.declarations.indexOf(dp.node), 1);
  if (decl.declarations.length === 0) {
    const i = list.indexOf(decl);
    if (i >= 0) list.splice(i, 1);
  }
}

function unwrapDispatcher(ast, d, freshName) {
  /* ---- 1. validate everything; no mutation until all checks pass ---- */
  const fePaths = new Map();
  const feNodes = new Set(d.fns.values());
  d.path.traverse({
    FunctionExpression(p) {
      if (feNodes.has(p.node)) {
        fePaths.set(p.node, p);
        p.skip();
      }
    },
  });
  const plans = new Map();
  for (const [key, fe] of d.fns) {
    const fp = fePaths.get(fe);
    if (!fp) return `fns entry ${key} not found`;
    const plan = planFunction(fp, d);
    if (typeof plan === "string") return `fns ${key}: ${plan}`;
    plans.set(key, plan);
  }

  if (writesOf(d.dispBinding).length) return "dispatcher reassigned";
  const order = new Map();
  let n = 0;
  traverse(ast, {
    Identifier(p) {
      order.set(p.node, n++);
    },
  });
  const sites = [];
  for (const rp of d.dispBinding.referencePaths) {
    const s = classifySite(rp, d, plans);
    if (typeof s === "string") return s;
    sites.push(s);
  }

  const consumed = new Set(sites.filter((s) => s.assignNode).map((s) => s.assignNode));
  const extraStmts = [];
  for (const r of d.payloadBinding.referencePaths)
    if (!r.isDescendant(d.path)) return "payload read outside dispatcher";
  for (const cv of d.payloadBinding.constantViolations) {
    if (consumed.has(cv.node)) continue;
    // inside a rebuilt function every payload write must be a rewritten call site
    if ([...fePaths.values()].some((fp) => cv.isDescendant(fp))) return "payload written inside dispatched function";
    if (cv.isDescendant(d.path)) continue;
    if (
      cv.isAssignmentExpression({ operator: "=" }) &&
      isUndefinedValue(cv.node.right) &&
      cv.parentPath.isExpressionStatement() &&
      Array.isArray(cv.parentPath.container)
    ) {
      extraStmts.push({ node: cv.parent, list: cv.parentPath.container });
      continue;
    }
    return "payload written outside dispatcher";
  }
  for (const r of d.cacheBinding.referencePaths)
    if (!r.isDescendant(d.path)) return "cache read outside dispatcher";
  for (const cv of d.cacheBinding.constantViolations) {
    if (cv.isDescendant(d.path)) continue;
    if (
      cv.isAssignmentExpression({ operator: "=" }) &&
      isObjectCreateNull(cv.node.right) &&
      cv.parentPath.isExpressionStatement() &&
      Array.isArray(cv.parentPath.container)
    ) {
      extraStmts.push({ node: cv.parent, list: cv.parentPath.container });
      continue;
    }
    return "cache written outside dispatcher";
  }

  /* ---- 2. rewrite call sites (pre-order: nested sites first) ---- */
  for (const plan of plans.values()) plan.name = freshName();
  sites.sort((a, b) => order.get(a.rp.node) - order.get(b.rp.node));
  for (const s of sites) {
    const id = t.identifier(plans.get(s.key).name);
    if (s.kind === "ref") {
      replaceChild(s.vpParent, s.vpNode, id);
    } else if (s.kind === "callNoArgs") {
      replaceChild(s.vpParent, s.vpNode, t.callExpression(id, []));
    } else {
      const call = t.callExpression(id, s.assignNode.right.elements);
      if (s.mode === "seq") {
        const exprs = s.seqNode.expressions;
        const i = exprs.indexOf(s.vpNode);
        if (i < 1 || exprs[i - 1] !== s.assignNode) throw new Error("dispatcher site moved");
        exprs.splice(i - 1, 2, call);
        if (exprs.length === 1) replaceChild(s.seqParent, s.seqNode, call);
      } else {
        const j = s.list.indexOf(s.stmtNode);
        if (j < 1 || s.list[j - 1] !== s.prevStmt) throw new Error("dispatcher site moved");
        s.list.splice(j - 1, 2, t.expressionStatement(call));
      }
    }
  }

  /* ---- 3. replace the dispatcher with the rebuilt functions ---- */
  const decls = [...plans.values()].map((p) => buildFunction(p, p.name));
  const list = d.path.container;
  list.splice(list.indexOf(d.node), 1, ...decls);
  for (const { node, list: l } of extraStmts) {
    const i = l.indexOf(node);
    if (i >= 0) l.splice(i, 1);
  }
  removeDeclarator(d.payloadBinding, isUndefinedValue);
  removeDeclarator(d.cacheBinding, (e) => e == null || isObjectCreateNull(e));
  return plans.size;
}

/* ================================================================== *
 * 9b. un-ParameterPacking (MovedDeclarations, PREDICTABLE functions)  *
 *     `function f(a, x, y = 0) { x = g(); … }` where no call ever      *
 *     passes the trailing params -> `var x; var y = 0;` in the body.   *
 *     Exact when every reference to f is a direct call/new with at     *
 *     most `index` plain arguments, and f uses no arguments/eval: the  *
 *     param then always starts undefined (or its static default).      *
 * ================================================================== */
/* js-virtualizer: lift virtualized functions back to JavaScript (lib/jsvirt-pass.mjs) */
pass("unJsVirtualizer", (ast, ctx) => {
  unJsVirtualizer(ast, ctx, { traverse, t, parse, recrawl });
});

pass("unParameterPacking", (ast, ctx) => {
  // JS-Confuser packs locals into extra parameters; undoing that on code it
  // didn't touch would rewrite real signatures (`function f(a = 1)` called
  // with no arguments here may still be called with some from another script)
  if (ctx.detected !== "js-confuser") return;
  recrawl(ast);
  let converted = 0;
  traverse(ast, {
    FunctionDeclaration(path) {
      const node = path.node;
      if (!node.id || !t.isBlockStatement(node.body)) return;
      const binding = path.parentPath.scope.getBinding(node.id.name);
      if (!binding || binding.path.node !== node || writesOf(binding).length) return;
      if (binding.referencePaths.length === 0) return;

      // highest argument count passed anywhere
      let maxArgs = 0;
      for (const rp of binding.referencePaths) {
        const call = rp.parentPath;
        if (!(call.isCallExpression() || call.isNewExpression()) || rp.key !== "callee") return;
        if (call.node.arguments.some((a) => !t.isExpression(a))) return; // spread
        maxArgs = Math.max(maxArgs, call.node.arguments.length);
      }

      // own `arguments` / any eval disqualifies
      let unsafe = false;
      path.traverse({
        Identifier(ip) {
          const n = ip.node.name;
          if (n === "eval" && !ip.scope.getBinding("eval")) unsafe = true;
          if (n === "arguments" && !ip.scope.getBinding("arguments")) {
            let f = ip.getFunctionParent();
            while (f && f.isArrowFunctionExpression()) f = f.parentPath.getFunctionParent();
            if (f === path) unsafe = true;
          }
        },
      });
      if (unsafe) return;

      // longest convertible suffix of params at index >= maxArgs
      const params = node.params;
      let from = params.length;
      while (from > maxArgs) {
        const p = params[from - 1];
        const ok =
          t.isIdentifier(p) ||
          (t.isAssignmentPattern(p) && t.isIdentifier(p.left) && simpleValueOf(p.right) !== null);
        if (!ok) break;
        from--;
      }
      if (from === params.length) return;

      const moved = params.splice(from);
      // a same-named function declaration in the body already declares it
      const declared = new Set(node.body.body.filter((st) => t.isFunctionDeclaration(st)).map((st) => st.id.name));
      const bare = moved.filter((p) => t.isIdentifier(p) && !declared.has(p.name));
      const inits = moved.filter((p) => t.isAssignmentPattern(p));
      node.body.body.unshift(
        ...bare.map((p) => t.variableDeclaration("var", [t.variableDeclarator(t.identifier(p.name))])),
        ...inits.map((p) =>
          t.variableDeclaration("var", [t.variableDeclarator(t.identifier(p.left.name), p.right)]),
        ),
      );
      converted += moved.length;
    },
  });
  ctx.stats.parameterPacking = { converted };
});

/* the rebuilt functions carry MovedDeclarations' `var x;` + `x = init;` */
{
  const md = passes.find((p) => p.name === "unMovedDeclarations").fn;
  pass("unMovedDeclarations#2", (ast, ctx, options) => {
    const before = ctx.stats.movedDeclarations?.inlined ?? 0;
    recrawl(ast);
    ctx.stats.movedDeclarations = { inlined: 0 };
    md(ast, ctx, options);
    ctx.stats.movedDeclarations = {
      inlined: before + (ctx.stats.movedDeclarations?.inlined ?? 0),
    };
  });
}

/* ================================================================== *
 * 10. GC: drop machinery with no references (pure initializers only)   *
 * ================================================================== */
pass("gc", (ast, ctx) => {
  recrawl(ast);
  let changed = true;
  let cycles = 0;
  let removedFns = 0;
  let removedVars = 0;
  while (changed && cycles++ < 60) {
    changed = false;
    recrawl(ast);
    traverse(ast, {
      FunctionDeclaration(path) {
        const id = path.node.id;
        if (!t.isIdentifier(id)) return;
        // resolve from the enclosing scope: the function's own scope may
        // hold a param/local reusing its name (renamer reuses names)
        const binding = fnDeclBinding(path);
        if (!binding || binding.referencePaths.length !== 0) return;
        path.remove();
        removedFns++;
        changed = true;
      },
      VariableDeclaration(path) {
        const node = path.node;
        if (node.declarations.length !== 1) return;
        if (t.isExportDeclaration(path.parentPath)) return;
        if (t.isForOfStatement(path.parentPath) || t.isForInStatement(path.parentPath))
          return;
        const dcl = node.declarations[0];
        if (!t.isIdentifier(dcl.id)) return;
        const binding = path.scope.getBinding(dcl.id.name);
        if (!binding) return;
        if (binding.referencePaths.length !== 0) return;
        if (writesOf(binding).length !== 0) return;
        const init = dcl.init;
        if (init === null || init === undefined) {
          path.remove();
          removedVars++;
          changed = true;
          return;
        }
        if (isRemovableInit(init)) {
          path.remove();
          removedVars++;
          changed = true;
        }
      },
    });
  }
  ctx.stats.gc = { fns: removedFns, vars: removedVars };

  function isRemovableInit(init) {
    if (
      t.isStringLiteral(init) ||
      t.isNumericLiteral(init) ||
      t.isBooleanLiteral(init) ||
      t.isNullLiteral(init)
    )
      return true;
    if (t.isIdentifier(init)) return true;
    if (t.isFunctionExpression(init)) return true;
    if (t.isObjectExpression(init) || t.isArrayExpression(init)) return true;
    if (
      t.isLogicalExpression(init, { operator: "||" }) &&
      t.isCallExpression(init.left) &&
      t.isObjectExpression(init.right) &&
      init.right.properties.length === 0
    )
      return true; // `getGlobal() || {}` machinery
    if (t.isCallExpression(init)) {
      // zero-ref var with call init: `getGlobal()` chains & IIFEs only —
      // require()/require.resolve() load modules (a real side effect) and
      // must never be treated as machinery
      const callee = init.callee;
      if (t.isIdentifier(callee, { name: "require" })) return false;
      if (t.isMemberExpression(callee) && !callee.computed &&
        t.isIdentifier(callee.object, { name: "require" })) return false;
      return true;
    }
    if (t.isMemberExpression(init)) return true;
    if (t.isNewExpression(init)) return true;
    return false;
  }
});

/* ================================================================== *
 * 11. normalize: computed string members/props -> dot form; tidy       *
 * ================================================================== */
pass("normalize", (ast) => {
  traverse(ast, {
    // `!![]` / `![]` (boolean literal obfuscation) — exact
    UnaryExpression: {
      exit(path) {
        const n = path.node;
        if (n.operator === "!" && t.isArrayExpression(n.argument) && n.argument.elements.length === 0) path.replaceWith(t.booleanLiteral(false));
        else if (n.operator === "!" && t.isBooleanLiteral(n.argument)) path.replaceWith(t.booleanLiteral(!n.argument.value));
      },
    },
    // `a, b, c;` as a statement -> `a; b; c;` — exact
    ExpressionStatement(path) {
      const e = path.node.expression;
      if (!t.isSequenceExpression(e)) return;
      if (!(path.parentPath.isBlockStatement() || path.parentPath.isProgram() || path.parentPath.isSwitchCase())) return;
      path.replaceWithMultiple(e.expressions.map((x) => t.expressionStatement(x)));
    },
    // `return a, b;` -> `a; return b;` (and `throw`) — exact
    "ReturnStatement|ThrowStatement"(path) {
      const e = path.node.argument;
      if (!t.isSequenceExpression(e)) return;
      if (!(path.parentPath.isBlockStatement() || path.parentPath.isProgram() || path.parentPath.isSwitchCase())) return;
      const last = e.expressions[e.expressions.length - 1];
      path.replaceWithMultiple([
        ...e.expressions.slice(0, -1).map((x) => t.expressionStatement(x)),
        path.isReturnStatement() ? t.returnStatement(last) : t.throwStatement(last),
      ]);
    },
    StringLiteral(path) {
      // print every string the same way (the obfuscators mix quote styles / escapes)
      if (path.node.extra && path.parentPath && !path.parentPath.isImportDeclaration() && !path.parentPath.isExportDeclaration()) delete path.node.extra;
    },
    NumericLiteral(path) {
      // hexadecimalNumbers: print 0x14 as 20 (same value)
      const raw = path.node.extra?.raw;
      if (raw && /^0[xX]/.test(raw)) delete path.node.extra;
    },
    MemberExpression(path) {
      const node = path.node;
      if (!node.computed) return;
      if (!t.isStringLiteral(node.property)) return;
      const v = node.property.value;
      if (!t.isValidIdentifier(v, false)) return; // reserved words are fine as property names
      node.property = t.identifier(v);
      node.computed = false;
    },
    ObjectProperty(path) {
      const node = path.node;
      if (node.computed && t.isStringLiteral(node.key)) node.computed = false;
      if (
        !node.computed &&
        t.isStringLiteral(node.key) &&
        t.isValidIdentifier(node.key.value, false)
      )
        node.key = t.identifier(node.key.value);
    },
    EmptyStatement(path) {
      path.remove();
      path.skip();
    },
  });
});

/* ================================================================== *
 * 11b. re-wrap unpacked code in its own function scope (see unPack)   *
 * ================================================================== */
pass("rePack", (ast, ctx) => {
  if (!ctx.packed) return;
  const iife = t.expressionStatement(
    t.callExpression(t.functionExpression(null, [], t.blockStatement(ast.program.body, ast.program.directives)), []),
  );
  t.addComment(iife, "leading", " unpacked: this code ran inside Function(), so it keeps its own function scope ", false);
  ast.program.body = [iife];
  ast.program.directives = [];
});

/* ================================================================== *
 * 12. rename: deterministic, unique, readable names per scope          *
 * ================================================================== */
/** a human-looking identifier: camelCase / PascalCase / CONSTANT_CASE, letters only (≥ 3 chars, has a vowel) */
function looksNatural(name) {
  if (/^[a-zA-Z]{1,2}$/.test(name)) return true; // i, j, x, el …
  if (!/[aeiouAEIOU]/.test(name)) return false;
  return /^[a-z]+(?:[A-Z][a-z]+)*$/.test(name) || /^(?:[A-Z][a-z]+)+$/.test(name) || /^[A-Z]+(?:_[A-Z]+)*$/.test(name);
}
pass("rename", (ast, ctx, options = {}) => {
  if (options.rename === false) return;
  // javascriptobfuscator.com keeps the program's original top-level names
  // (`var msg`, `function greet` restored by unJsobNameRestore) — renaming
  // them would discard recovered names and change the global surface.
  if (ctx.detected === "jsobfuscator-com" && options.rename !== true) return;
  recrawl(ast);

  const used = new Set();
  traverse(ast, {
    Identifier(p) {
      used.add(p.node.name);
    },
  });

  const letters = "abcdefghijklmnopqrstuvwxyz";
  let i = 0;
  function nextName() {
    while (true) {
      const cycle = Math.floor(i / 26);
      const ch = letters[i % 26];
      i++;
      const n = cycle === 0 ? ch : ch + String(cycle);
      if (!used.has(n)) {
        used.add(n);
        return n;
      }
    }
  }

  let renamed = 0;
  traverse(ast, {
    Program: {
      enter(programPath) {
        programPath.scope.crawl();
        // collect scopes deterministically via traversal
        const scopes = new Set();
        traverse(ast, {
          enter(path) {
            if (path.scope) scopes.add(path.scope);
          },
        });

        for (const scope of scopes) {
          for (const [name, binding] of Object.entries(scope.bindings)) {
            if (name === "undefined" || name === "eval" || name === "arguments")
              continue;
            if (binding.kind === "module") continue;
            // a class declaration's own-name binding inside the class shares
            // its id node with the outer binding: renamed together below
            if (!options.renameAll && looksNatural(name)) continue; // keep real names (obfuscator.io keeps globals)
            const isClass = binding.path.isClassDeclaration();
            if (isClass && scope.path === binding.path) continue; // the class-internal one
            try {
              const fresh = nextName();
              const inner = isClass ? binding.path.scope.getOwnBinding(name) : null;
              scope.rename(name, fresh);
              if (inner && inner !== binding) binding.path.scope.rename(name, fresh);
              renamed++;
            } catch {
              /* keep original name on failure */
            }
          }
        }
      },
    },
  });
  ctx.stats.rename = { renamed };
});

/* ---------------------------------------------------------------- run */

/** passes that only tidy the final result: run once, after the fixpoint */
const FINAL_PASSES = new Set(["normalize", "rePack", "rename"]);
const MAX_ROUNDS = 12; // rounds only continue while the code still changes

/**
 * Run the reversal passes to a fixpoint: undoing one layer can expose
 * another (e.g. a CFF machine inside a dispatched function only becomes
 * recognisable after the dispatcher is unwrapped). Every pass rewrites only
 * shapes it can prove, so repeating is safe. Errors are reported from the
 * last round only (earlier ones may have been resolved by later rounds);
 * numeric stats are summed across rounds.
 */
export function runAllPasses(ast, ctx, options = {}) {
  const timing = process.env.PASSTIME ? (globalThis.__passTime = globalThis.__passTime || {}) : null;
  // PASSTRACE=<text>: report the pass that makes <text> appear / disappear (debug)
  const trace = process.env.PASSTRACE || null;
  let traceHas = trace ? generate(ast).includes(trace) : false;
  let traceRound = 0;
  const runPass = (name, fn, c) => {
    const t0 = timing ? performance.now() : 0;
    const traceBefore = trace && process.env.PASSTRACE_DUMP ? generate(ast) : null;
    try {
      fn(ast, c, options);
      if (trace) {
        if (traceBefore !== null && generate(ast).includes(trace) !== traceHas) process.getBuiltinModule("fs").writeFileSync(process.env.PASSTRACE_DUMP, traceBefore);
        const has = generate(ast).includes(trace);
        if (has !== traceHas) console.error(`PASSTRACE round ${traceRound} ${name}: ${has ? "appeared" : "removed"}`);
        traceHas = has;
      }
      if (timing) timing[name] = (timing[name] || 0) + performance.now() - t0;
    } catch (err) {
      c.errors.push(`${name}: ${err && err.stack ? err.stack.split("\n").slice(0, process.env.FULLSTACK ? 30 : 3).join(" | ") : err}`);
    }
  };
  const merge = (into, from) => {
    for (const [k, v] of Object.entries(from)) {
      if (v && typeof v === "object" && !Array.isArray(v)) merge((into[k] = into[k] || {}), v);
      else if (typeof v === "number" && typeof into[k] === "number") into[k] += v;
      else if (Array.isArray(v) && Array.isArray(into[k])) into[k] = [...new Set([...into[k], ...v])];
      else if (v !== "" && v !== undefined) into[k] = v;
    }
  };
  const core = passes.filter((p) => !FINAL_PASSES.has(p.name));
  let before = generate(ast);
  for (let round = 0; round < MAX_ROUNDS; round++) {
    const roundCtx = { ...ctx, stats: {}, errors: [] };
    traceRound = round;
    let stopped = false;
    for (const { name, fn } of core) {
      if (options.stopBefore === name) {
        stopped = true;
        break;
      }
      runPass(name, fn, roundCtx);
    }
    merge(ctx.stats, roundCtx.stats);
    ctx.errors = roundCtx.errors;
    if (roundCtx.packed) ctx.packed = true;
    if (stopped) return;
    const after = generate(ast);
    if (after === before) break;
    before = after;
  }
  for (const { name, fn } of passes) {
    if (!FINAL_PASSES.has(name)) continue;
    if (options.stopBefore === name) return;
    runPass(name, fn, ctx);
  }
}
export function deobfuscate(code, options = {}) {
  // JSFuck input (only []()!+) cannot go through Babel meaningfully: recover
  // the program inside it first (safely, without executing it), then run the
  // normal pipeline over the recovered source. canUnwrap lets a zero-argument
  // payload run at the top level instead of as an IIFE — see canRunAtTopLevel.
  if (isJsfuck(code)) return deobfuscateJsfuck(code, options);
  // Same idea for the whole-program encoders: each is a pure string-level
  // encoding of the source, so decode statically (never executing anything),
  // then run the normal pipeline over the recovered program.
  if (isPacker(code)) return deobfuscatePacker(code, options);
  if (isJjencode(code)) return deobfuscateWholeProgram(code, options, "jjencode", decodeJjencode);
  if (isAaencode(code)) return deobfuscateWholeProgram(code, options, "aaencode", decodeAaencode);
  if (isJfogs(code)) return deobfuscateWholeProgram(code, options, "jfogs", unJfogs);
  if (isJsdefender(code)) return deobfuscateJsdefender(code, options);
  const ast = parse(code);
  const ctx = { stats: {}, errors: [], detected: detectObfuscator(code).best?.id ?? null };
  // companion files (e.g. a js-virtualizer VM): deobfuscate them too, then
  // read their opcode tables
  if (options.companions && options.companions.length) {
    ctx.jsvTables = [];
    for (const text of options.companions) {
      let table = opNamesFromVmSource(text);
      if (!table) {
        try { table = opNamesFromVmSource(deobfuscate(text, { rename: false }).code); } catch { table = null; }
      }
      if (table) ctx.jsvTables.push(table);
    }
  }
  runAllPasses(ast, ctx, options);
  const out = generate(ast);
  return { code: out, stats: ctx.stats, errors: ctx.errors };
}

/**
 * Can `body` (the recovered JSFuck payload) run as top-level statements in the
 * output instead of inside `(function () { … })()`? Exact check: `Function`
 * bodies run in sloppy mode with `var` / function declarations landing on the
 * global object — the same thing script top-level does — so those may unwrap.
 * Must wrap for: return (syntax error at top level), let/const/class
 * declarations (they would leak into the global lexical environment instead of
 * staying function-local), and this / arguments / eval at the top level (they
 * mean different things inside a Function body). Nested functions are skipped
 * — they keep their own scope.
 */
function canRunAtTopLevel(body) {
  let ast;
  try {
    ast = parse(body);
  } catch {
    return false;
  }
  const bad = (node, isTop) => {
    if (!node || typeof node !== "object") return false;
    if (Array.isArray(node)) return node.some((n) => bad(n, isTop));
    if (typeof node.type !== "string") return false;
    if (node.type === "ThisExpression" || (node.type === "Identifier" && node.name === "arguments")) return isTop;
    if (node.type === "Identifier" && node.name === "eval") return true; // direct vs indirect eval
    // nested function boundaries restart the "top level" meaning
    if (node.type === "FunctionDeclaration" || node.type === "FunctionExpression" || node.type === "ArrowFunctionExpression" || node.type === "ClassDeclaration" || node.type === "ClassExpression")
      isTop = false;
    for (const key of Object.keys(node)) {
      if (key === "loc" || key === "start" || key === "end" || key === "leadingComments" || key === "trailingComments" || key === "innerComments") continue;
      if (bad(node[key], isTop)) return true;
    }
    return false;
  };
  for (const st of ast.program.body) {
    if (st.type === "ReturnStatement") return false;
    if (st.type === "VariableDeclaration" && st.kind !== "var") return false;
    if (st.type.endsWith("Declaration") && st.type !== "FunctionDeclaration" && st.type !== "VariableDeclaration") return false;
    if (bad(st, true)) return false;
  }
  return true;
}

function deobfuscateJsfuck(code, options = {}) {
  const r = unJsfuck(code, canRunAtTopLevel);
  if (r.error) throw new Error(`JSFuck: ${r.error}`);
  // The recovered payload IS the original source (exact names included), so
  // default to keeping its names: rename only when explicitly requested.
  const opts = { ...options, rename: options.rename === true ? true : false };
  const ast = parse(r.code);
  const ctx = { stats: { jsfuck: { recovered: r.payloads } }, errors: [], detected: "jsfuck" };
  runAllPasses(ast, ctx, opts);
  const out = generate(ast);
  return { code: out, stats: ctx.stats, errors: ctx.errors };
}

// --- whole-program encoders: Dean Edwards' Packer, JJEncode, AAEncode -------

function isPacker(code) {
  // eval((function(p,a,c,k,e,d){…})(…)) — the classic single-paren form too
  return /^\s*eval\s*\(\s*\(?\s*function\s*\(\s*p\s*,\s*a\s*,\s*c\s*,\s*k\b/.test(code);
}

function isJjencode(code) {
  const c = code.trimStart();
  // plain form: <prefix>=~[];…  — or the demo page's palindrome wrapper,
  // which begins with the 3 bytes "'\ (LEAD = 34,39,92,34,43,39,43,34,44)
  return /^[\w$]+=~\[\];/.test(c) || (c.startsWith("\"'\\") && c.includes("=~[];"));
}

function isAaencode(code) {
  return code.includes("ﾟωﾟﾉ") && code.includes("(ﾟДﾟ)");
}

function deobfuscatePacker(code, options = {}) {
  const recovered = unpackPacker(code.trim());
  const opts = { ...options, rename: options.rename === true ? true : false };
  const ast = parse(recovered);
  const ctx = { stats: { packer: { recovered: true } }, errors: [], detected: "packer" };
  runAllPasses(ast, ctx, opts);
  const out = generate(ast);
  return { code: out, stats: ctx.stats, errors: ctx.errors };
}

/**
 * PreEmptive JSDefender (lib/jsdefender.mjs, lib/jsd-cff.mjs): peel the
 * self-defending eval loaders (decrypted statically), fold the runtime's
 * constant helpers and string table (pure-subset evaluator, never native
 * execution), restructure its state machines, then the normal pipeline.
 */
function deobfuscateJsdefender(code, options) {
  const peeled = peelJsdefender(code);
  const ast = parse(peeled.code);
  const ctx = { stats: {}, errors: [...peeled.errors], detected: "jsdefender" };
  // Machines nest (a case body holds another machine), so structuring one exposes
  // the next; folding exposes new constant transitions. Interleave to a fixpoint.
  let folded = foldJsdefenderHelpers(ast);
  let machines = 0;
  for (let r = 0; r < 60; r++) {
    const n = unflattenJsdefender(ast);
    machines += n;
    const f = foldJsdefenderHelpers(ast);
    folded += f;
    if (!n && !f) break;
  }
  tidyLoops(ast);
  runAllPasses(ast, ctx, options);
  const deadDecls = eliminateDeadDeclarations(ast);
  ctx.stats.jsdefender = { layers: peeled.layers, folded, machines, deadDecls };
  return { code: generate(ast), stats: ctx.stats, errors: ctx.errors };
}

function deobfuscateWholeProgram(code, options, id, decode) {
  let recovered;
  try {
    recovered = decode(code.trim());
  } catch (e) {
    throw new Error(e.message); // decode errors already carry the encoder name
  }
  const opts = { ...options, rename: options.rename === true ? true : false };
  const ast = parse(recovered);
  const ctx = { stats: { [id]: { recovered: true } }, errors: [], detected: id };
  runAllPasses(ast, ctx, opts);
  const out = generate(ast);
  return { code: out, stats: ctx.stats, errors: ctx.errors };
}
