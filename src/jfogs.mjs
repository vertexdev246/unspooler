/**
 * jfogs reverser — static, exact, no execution.
 *
 * jfogs (npm 1.0.0-alpha.5, github.com/zswang/jfogs) rewrites a whole program
 * into a single IIFE:
 *
 *   (function ($fog$<sentinel>, $fog$0 … $fog$(N-1)) {
 *     if ("‮" !== $fog$<sentinel>) { return; }
 *     [decode prologue]
 *     <original program with every extracted string/number/boolean/null and
 *      every non-computed member property (obj.log → obj[$fog$k]) replaced by
 *      a $fog$k parameter reference>
 *   })("‮", <literal arguments>);
 *
 * Values travel positionally; sloppy-mode arguments linkage lets the prologue's
 * mutations of `arguments` write back into the parameters, which is how decoded
 * strings reach the body. The decoder computes those final parameter values
 * statically (the prologue's arithmetic is fixed) and inlines the literals back
 * into the body:
 *
 *   default : param[i] = arg[i]                        (sentinel is arg 0)
 *   reverse : param[i] = maybe-reversed arg[N-1-i]     (string args reversed
 *             in place first, then argument positions swapped)
 *   zero    : param[i] = zero-width-decoded arg[i]     (7 bits per char, or
 *             8 bits + UTF-8 recombination when any recorded value contains a
 *             char ≥ U+0100 — visible in the /.{7}/ vs /.{8}/ argument)
 *
 * zero-without-strings emits no sentinel and no prologue at all (plain
 * positional identity). `options.breakout` adds a `var $fog$X = {};` wrapper
 * (trailing `B.name = name` statements inside the IIFE and `var name = B.name`
 * after it) — dropped, because unwrapping the IIFE restores the original
 * top-level bindings anyway.
 *
 * Known encoder bugs are reproduced exactly (behavior of the artifact):
 *   - zero type with Latin-1 chars mixes 8-bit char codes into a fixed 7-bit
 *     decoder ("héllo" runs as "h4v671"); we decode with the artifact's own
 *     semantics, garbage included;
 *   - String.prototype.replace coerces the char map's undefined lookups to the
 *     literal text "undefined".
 *
 * Anything deviating from the generated shapes is a hard error. Regex-valued
 * parameters are hoisted as `var $fog$k = /…/;` so the body keeps sharing one
 * RegExp object (a regex literal would create a fresh one per evaluation).
 */

const require = (await import("module")).createRequire(import.meta.url);
const parser = require("@babel/parser");
const t = require("@babel/types");
const babelGenerate = require("@babel/generator").default;

const NAME_RE = /^\$fog\$(\d+)$/;
const SENTINEL = "\u202e";

function fail(msg) {
  throw new Error(`jfogs: ${msg}`);
}

// ---------------------------------------------------------------- walking

const SKIP_KEYS = new Set([
  "loc", "start", "end", "range", "extra",
  "leadingComments", "trailingComments", "innerComments",
]);

/** children of `node` as [value, key, indexOrNull] */
function children(node) {
  const out = [];
  for (const key of Object.keys(node)) {
    if (SKIP_KEYS.has(key)) continue;
    const v = node[key];
    if (Array.isArray(v)) {
      v.forEach((el, i) => { if (el && typeof el === "object") out.push([el, key, i]); });
    } else if (v && typeof v === "object" && typeof v.type === "string") {
      out.push([v, key, null]);
    }
  }
  return out;
}

/** positions where an Identifier is a variable reference (not a name/binding) */
function isRefPosition(node, parent, key) {
  if (node.type !== "Identifier" || !parent) return false;
  switch (parent.type) {
    case "MemberExpression":
      return parent.computed || key !== "property";
    case "ObjectProperty":
    case "ObjectMethod":
    case "ClassProperty":
    case "ClassMethod":
      if (key === "key") return parent.computed || parent.shorthand;
      return true;
    case "LabeledStatement":
    case "BreakStatement":
    case "ContinueStatement":
      return key !== "label";
    case "VariableDeclarator":
      return key !== "id";
    case "FunctionDeclaration":
    case "FunctionExpression":
    case "ArrowFunctionExpression":
    case "ClassDeclaration":
    case "ClassExpression":
      if (key === "id" || key === "params") return false;
      return true;
    case "CatchClause":
      return key !== "param";
    default:
      return true;
  }
}

/**
 * Walk a subtree. `visit(node, parent, key, replace)` is called for every
 * reference-position Identifier; `replace(newNode)` swaps it in its parent.
 * Non-reference identifier positions (labels, keys, bindings) are skipped.
 */
function walkRefs(root, visit) {
  const rec = (node, parent, key, replace) => {
    if (!node || typeof node.type !== "string") return;
    if (node.type === "Identifier" && isRefPosition(node, parent, key)) {
      if (visit(node, parent, key, replace)) return; // visitor replaced it
    }
    for (const [child, cKey, index] of children(node)) {
      const assign = (nn) => {
        if (index === null) node[cKey] = nn;
        else node[cKey][index] = nn;
      };
      rec(child, node, cKey, assign);
    }
  };
  rec(root, null, null, null);
}

/** names bound by a pattern (identifier / destructuring) */
function addPatternNames(node, set) {
  if (!node) return;
  if (node.type === "Identifier") { set.add(node.name); return; }
  if (node.type === "AssignmentPattern") return addPatternNames(node.left, set);
  if (node.type === "RestElement") return addPatternNames(node.argument, set);
  if (node.type === "ArrayPattern") return node.elements.forEach((el) => addPatternNames(el, set));
  if (node.type === "ObjectPattern") {
    for (const prop of node.properties) {
      if (prop.type === "RestElement") addPatternNames(prop.argument, set);
      else addPatternNames(prop.value, set); // key is a name, not a binding
    }
  }
}

/** every name bound anywhere in the subtree (var/let/const/fn/class/catch) */
function collectBindings(root) {
  const set = new Set();
  const rec = (node) => {
    if (!node || typeof node.type !== "string") return;
    switch (node.type) {
      case "VariableDeclarator": addPatternNames(node.id, set); break;
      case "FunctionDeclaration":
      case "FunctionExpression":
      case "ArrowFunctionExpression":
        addPatternNames(node.id, set);
        node.params.forEach((p) => addPatternNames(p, set));
        break;
      case "ClassDeclaration":
      case "ClassExpression":
        addPatternNames(node.id, set);
        break;
      case "CatchClause": addPatternNames(node.param, set); break;
    }
    for (const [child] of children(node)) rec(child);
  };
  rec(root);
  return set;
}

// ------------------------------------------------------------- arg values

function argValue(node, what) {
  if (t.isStringLiteral(node)) return { kind: "string", value: node.value };
  if (t.isNumericLiteral(node)) return { kind: "number", value: node.value };
  if (t.isBooleanLiteral(node)) return { kind: "boolean", value: node.value };
  if (t.isNullLiteral(node)) return { kind: "null" };
  if (t.isRegExpLiteral(node)) return { kind: "regex", pattern: node.pattern, flags: node.flags };
  fail(`${what} is not a plain literal (${node.type}) — unknown argument shape`);
}

function valueNode(v) {
  switch (v.kind) {
    case "string": return t.stringLiteral(v.value);
    case "number": return t.numericLiteral(v.value);
    case "boolean": return t.booleanLiteral(v.value);
    case "null": return t.nullLiteral();
    case "regex": return t.regExpLiteral(v.pattern, v.flags);
    default: throw new Error(`jfogs: cannot build node for ${v.kind}`);
  }
}

// ------------------------------------------------- artifact runtime math

/** code-unit reversal, exactly as "".split("").reverse().join("") does */
function revCodeUnits(s) {
  return s.split("").reverse().join("");
}

/**
 * Zero-width decode with the artifact's exact semantics: every char maps to
 * "0"/"1"/"undefined" (replace coerces undefined), then fixed-width groups are
 * parseInt(…, 2) → fromCharCode. 8-bit runs recombine UTF-8 afterwards.
 * Latin-1 input garbles exactly like the artifact ("héllo" → "h4v671").
 */
function zeroDecode(s, bits) {
  let out = s.replace(/./g, (a) => ({ "\u200c": "0", "\u200d": "1" }[a]));
  out = out.replace(new RegExp(`.{${bits}}`, "g"), (a) => String.fromCharCode(parseInt(a, 2)));
  if (bits === 8) {
    out = out.replace(/[\u00c0-\u00df][\u0080-\u00bf]/g, (c) =>
      String.fromCharCode(((c.charCodeAt(0) & 0x1f) << 6) | (c.charCodeAt(1) & 0x3f)));
    out = out.replace(/[\u00e0-\u00ef][\u0080-\u00bf]{2}/g, (c) =>
      String.fromCharCode(((c.charCodeAt(0) & 0x0f) << 12) | ((c.charCodeAt(1) & 0x3f) << 6) | (c.charCodeAt(2) & 0x3f)));
  }
  return out;
}

// ------------------------------------------------------- prologue shapes

function paramIndexOf(name, nameToIndex) {
  const idx = nameToIndex.get(name);
  return idx === undefined ? -1 : idx;
}

/** numeric suffix of a $fog$<n> name */
function nameNum(name) {
  const m = NAME_RE.exec(name);
  return m ? Number(m[1]) : -1;
}

/** refs of a statement to parameter positions */
function stmtParamRefs(stmt, nameToIndex) {
  const refs = new Set();
  walkRefs(stmt, (node) => {
    const idx = paramIndexOf(node.name, nameToIndex);
    if (idx >= 0) refs.add(idx);
    return false;
  });
  return refs;
}

function matchGuard(stmt, nameToIndex) {
  if (!t.isIfStatement(stmt) || stmt.alternate) return -1;
  if (!t.isBinaryExpression(stmt.test, { operator: "!==" })) return -1;
  const { left, right } = stmt.test;
  if (!t.isStringLiteral(left, { value: SENTINEL }) || !t.isIdentifier(right)) return -1;
  if (!Array.isArray(stmt.consequent.body) || stmt.consequent.body.length !== 1) return -1;
  if (!t.isReturnStatement(stmt.consequent.body[0]) || stmt.consequent.body[0].argument) return -1;
  return paramIndexOf(right.name, nameToIndex);
}

/** var P = arguments; — P is a fresh decoder var, so check its numeric suffix (user values occupy $fog$0…N-1) */
function isVarArguments(stmt, minIndex) {
  if (!t.isVariableDeclaration(stmt, { kind: "var" }) || stmt.declarations.length !== 1) return false;
  const d = stmt.declarations[0];
  return t.isIdentifier(d.id) && nameNum(d.id.name) >= minIndex &&
    t.isIdentifier(d.init, { name: "arguments" });
}

/** var P; */
function isVarEmpty(stmt, minIndex) {
  if (!t.isVariableDeclaration(stmt, { kind: "var" }) || stmt.declarations.length !== 1) return false;
  const d = stmt.declarations[0];
  return d.init == null && t.isIdentifier(d.id) && nameNum(d.id.name) >= minIndex;
}

/** subtree contains a node shape */
function subtreeHas(node, pred) {
  let found = false;
  const rec = (n) => {
    if (found || !n || typeof n.type !== "string") return;
    if (pred(n)) { found = true; return; }
    for (const [child] of children(n)) rec(child);
  };
  rec(node);
  return found;
}

// reverse string loop: `typeof argv[i] === P`
const looksLikeStringLoop = (st) => subtreeHas(st, (n) =>
  n.type === "BinaryExpression" && n.operator === "===" &&
  n.left.type === "UnaryExpression" && n.left.operator === "typeof");
// reverse swap loop: `i < len / 2`
const looksLikeSwapLoop = (st) => subtreeHas(st, (n) =>
  n.type === "BinaryExpression" && n.operator === "/");
// zero decode loop: the { '\u200c': 0, '\u200d': 1 } char map
const looksLikeZeroLoop = (st) => subtreeHas(st, (n) =>
  n.type === "ObjectExpression" && n.properties.length === 2 &&
  n.properties.every((p) => p.type === "ObjectProperty" &&
    (p.key.value === "\u200c" || p.key.value === "\u200d")));

function isPrologueFor(stmt, nameToIndex, minIndex, pred) {
  if (!t.isForStatement(stmt)) return false;
  if (stmt.test == null || stmt.update == null) return false;
  const refs = stmtParamRefs(stmt, nameToIndex);
  if (refs.size === 0 || [...refs].some((i) => i < minIndex)) return false;
  return pred(stmt);
}

// ------------------------------------------------------------------ main

/**
 * Parse the artifact and return { variant, fn, call, nameToIndex, N, args,
 * prologueEnd, breakout } — or throw. Structural only; decoding happens after.
 */
function analyze(code) {
  let ast;
  try {
    ast = parser.parse(code, { allowReturnOutsideFunction: true, sourceType: "script" });
  } catch (e) {
    fail(`does not parse (${e.message})`);
  }
  const stmts = ast.program.body;

  // -- breakout wrapper: var $fog$X = {}; <IIFE>; var name = $fog$X.name; …
  let breakout = null;
  let i = 0;
  if (
    t.isVariableDeclaration(stmts[0], { kind: "var" }) &&
    stmts[0].declarations.length === 1 &&
    t.isIdentifier(stmts[0].declarations[0].id) &&
    NAME_RE.test(stmts[0].declarations[0].id.name) &&
    t.isObjectExpression(stmts[0].declarations[0].init) &&
    stmts[0].declarations[0].init.properties.length === 0
  ) {
    breakout = { obj: stmts[0].declarations[0].id.name, inside: [], outside: [] };
    i = 1;
  }

  const iifeStmt = stmts[i];
  if (!iifeStmt || !t.isExpressionStatement(iifeStmt) || !t.isCallExpression(iifeStmt.expression) ||
    !t.isFunctionExpression(iifeStmt.expression.callee)) {
    fail("program is not a single (function (…) {…})(…) IIFE");
  }
  const trailing = stmts.slice(i + 1);

  const fn = iifeStmt.expression.callee;
  const call = iifeStmt.expression;
  if (fn.params.length !== call.arguments.length) {
    fail(`parameter count ${fn.params.length} !== argument count ${call.arguments.length}`);
  }

  const nameToIndex = new Map();
  fn.params.forEach((p, idx) => {
    if (!t.isIdentifier(p) || !NAME_RE.test(p.name)) {
      fail(`parameter #${idx} is not a $fog$<n> identifier — unknown shape`);
    }
    if (nameToIndex.has(p.name)) fail(`duplicate parameter ${p.name}`);
    nameToIndex.set(p.name, idx);
  });

  const args = call.arguments.map((a, idx) => {
    if (t.isIdentifier(a)) {
      // String / parseInt are pushed verbatim for internal prologue positions
      return { kind: "ident", name: a.name };
    }
    return argValue(a, `argument #${idx}`);
  });

  return { ast, stmts, breakout, trailing, fn, call, nameToIndex, args };
}

function decodeJfogsProgram(code) {
  const { stmts, breakout, trailing, fn, call, nameToIndex, args } = analyze(code);
  const fstmts = fn.body.body;
  const paramCount = fn.params.length;
  if (paramCount !== args.length) fail("parameter/argument mismatch"); // already equal, paranoia

  // ---- resolve variant
  let variant; // "default" | "reverse" | "zero" | "plain"
  let N; // number of value parameters
  let prologueEnd = 0;

  const guardIdx = fstmts.length ? matchGuard(fstmts[0], nameToIndex) : -1;
  if (guardIdx === 0) {
    // default type: sentinel is parameter 0, values are 1..end, no prologue
    variant = "default";
    N = paramCount;
    if (!t.isStringLiteral(call.arguments[0], { value: SENTINEL })) {
      fail("guard sentinel parameter is not fed the \\u202e argument");
    }
    prologueEnd = 1;
  } else if (guardIdx > 0) {
    // reverse / zero: sentinel is parameter N, arg N+1 repeats N
    variant = null;
    N = guardIdx;
    if (!t.isStringLiteral(call.arguments[N], { value: SENTINEL })) {
      fail("sentinel argument position does not carry \\u202e");
    }
    const lenArg = args[N + 1];
    if (!lenArg || lenArg.kind !== "number" || lenArg.value !== N) {
      fail(`self-describing length argument missing at position ${N + 1} (expected ${N})`);
    }
    // walk the fixed prologue sequence to find where the body starts
    let pos = 1;
    if (!isVarArguments(fstmts[pos], N)) {
      fail(`expected "var $fog$k = arguments;" after the guard, got ${fstmts[pos] && fstmts[pos].type}`);
    }
    pos++;
    if (isVarEmpty(fstmts[pos], N)) {
      // reverse: var argv; var index; [for-strings]; for-swap
      variant = "reverse";
      pos++;
      if (isPrologueFor(fstmts[pos], nameToIndex, N, looksLikeStringLoop)) pos++;
      if (!isPrologueFor(fstmts[pos], nameToIndex, N, looksLikeSwapLoop)) {
        fail("reverse prologue does not end with the swap loop — unknown shape");
      }
      pos++;
    } else if (isPrologueFor(fstmts[pos], nameToIndex, N, looksLikeZeroLoop)) {
      variant = "zero";
      pos++;
    } else {
      fail("prologue after the guard matches neither the reverse nor the zero template");
    }
    prologueEnd = pos;
  } else {
    // no guard: zero-without-strings — plain positional identity.
    // (reverse always emits the guard; default always emits the sentinel.)
    variant = "plain";
    N = paramCount;
    prologueEnd = 0;
  }

  // ---- compute final parameter values
  const finals = new Array(paramCount); // param index → value kind/value
  const valueAt = (i, what) => {
    const a = args[i];
    if (a.kind === "ident") fail(`${what} is an identifier argument (${a.name}) in a value position`);
    return a;
  };
  if (variant === "default") {
    for (let i = 1; i < paramCount; i++) finals[i] = valueAt(i, `argument #${i}`);
  } else if (variant === "plain") {
    for (let i = 0; i < paramCount; i++) finals[i] = valueAt(i, `argument #${i}`);
  } else if (variant === "reverse") {
    // strings reversed in place at 0..N-1, then positions swapped
    for (let i = 0; i < N; i++) {
      const v = valueAt(N - 1 - i, `argument #${N - 1 - i}`);
      finals[i] = v.kind === "string" ? { kind: "string", value: revCodeUnits(v.value) } : v;
    }
  } else {
    // zero: decode string args; bit width comes from the /.{7}/ or /.{8}/ argument
    let bits = 0;
    for (let i = N + 1; i < paramCount; i++) {
      const a = args[i];
      if (a.kind === "regex" && /^\.\{\d\}$/.test(a.pattern)) {
        bits = Number(a.pattern.slice(2, -1));
        break;
      }
    }
    if (bits !== 7 && bits !== 8) fail("zero prologue without a /.{7}/g or /.{8}/g argument");
    for (let i = 0; i < N; i++) {
      const v = valueAt(i, `argument #${i}`);
      finals[i] = v.kind === "string" ? { kind: "string", value: zeroDecode(v.value, bits) } : v;
    }
  }

  // ---- split off the body
  const body = fstmts.slice(prologueEnd);

  // breakout: trailing `B.name = name;` statements at the end of the IIFE
  if (breakout) {
    while (body.length) {
      const st = body[body.length - 1];
      if (!(t.isExpressionStatement(st) && t.isAssignmentExpression(st.expression, { operator: "=" }))) break;
      const { left, right } = st.expression;
      if (!(t.isMemberExpression(left) && !left.computed && t.isIdentifier(left.object, { name: breakout.obj }) &&
        t.isIdentifier(left.property) && t.isIdentifier(right))) break;
      breakout.inside.unshift(right.name);
      body.pop();
    }
  }

  // ---- validate the body
  const minIndex = variant === "default" ? 1 : 0;
  for (const st of body) {
    walkRefs(st, (node) => {
      const idx = paramIndexOf(node.name, nameToIndex);
      if (node.name === "arguments") {
        if (variant === "reverse" || variant === "zero") {
          fail("body references `arguments`, which the prologue mutates — cannot decode statically");
        }
      } else if (idx >= 0 && idx < minIndex) {
        fail(`body references ${node.name}, which is not a value parameter — shape mismatch`);
      } else if (idx < 0 && NAME_RE.test(node.name) && node.name !== breakout?.obj) {
        fail(`body references ${node.name}, which is not a parameter — unknown shape`);
      }
      return false;
    });
  }
  const bound = collectBindings({ type: "Program", body });
  for (const name of bound) {
    if (nameToIndex.has(name)) fail(`body redeclares ${name} — substitution would be unsafe`);
  }

  // breakout outside vars must mirror the inside assignments exactly
  if (breakout) {
    if (!breakout.inside.length) fail("breakout wrapper present but no B.name = name assignments found");
    const names = [];
    for (const st of trailing) {
      if (!(t.isVariableDeclaration(st, { kind: "var" }) && st.declarations.length === 1)) {
        fail(`unexpected statement after the IIFE (${st.type}) — not a breakout export`);
      }
      const d = st.declarations[0];
      if (!(t.isIdentifier(d.id) && t.isMemberExpression(d.init) && !d.init.computed &&
        t.isIdentifier(d.init.object, { name: breakout.obj }) && t.isIdentifier(d.init.property) &&
        d.init.property.name === d.id.name)) {
        fail(`unexpected statement after the IIFE — not a "var name = B.name" export`);
      }
      names.push(d.id.name);
    }
    if (names.length !== breakout.inside.length || names.some((n, k) => n !== breakout.inside[k])) {
      fail("breakout export names differ between the IIFE tail and the trailing vars");
    }
  } else if (trailing.length) {
    fail(`unexpected statement after the IIFE (${trailing[0].type})`);
  }

  // ---- hoist regex-valued parameters so the body keeps one shared RegExp
  const regexNames = [];
  for (let i = 0; i < paramCount; i++) {
    if (finals[i] && finals[i].kind === "regex") {
      const name = fn.params[i].name;
      let used = false;
      for (const st of body) {
        walkRefs(st, (node) => { if (node.name === name) used = true; return false; });
        if (used) break;
      }
      if (used) regexNames.push({ name, value: finals[i] });
    }
  }

  // ---- substitute literal values for parameter references
  const subst = new Map();
  for (let i = 0; i < paramCount; i++) {
    const v = finals[i];
    if (!v || v.kind === "regex") continue; // regexes stay identifiers (hoisted var)
    const name = fn.params[i].name;
    subst.set(name, () => valueNode(v));
  }
  for (const st of body) {
    walkRefs(st, (node, parent, key, replace) => {
      const make = subst.get(node.name);
      if (make) { replace(make()); return true; }
      return false;
    });
  }

  const out = [];
  for (const { name, value } of regexNames) {
    out.push(t.variableDeclaration("var", [t.variableDeclarator(t.identifier(name), valueNode(value))]));
  }
  out.push(...body);

  const generated = babelGenerate(t.program(out), { compact: false, minified: false, comments: true }).code;
  return { code: generated, variant };
}

export function unJfogs(code) {
  return decodeJfogsProgram(String(code)).code;
}

export function isJfogs(code) {
  if (typeof code !== "string" || !/\$fog\$\d/.test(code)) return false;
  try {
    decodeJfogsProgram(code);
    return true;
  } catch {
    return false;
  }
}
