/**
 * gnirts reverser — static fold, no execution.
 *
 * gnirts (npm 1.1.8, github.com/anseki/gnirts) only touches code between
 * `/* @mangle *​/ … /* @/mangle *​/` directives, replacing each marked string
 * literal with a pure-arithmetic expression that rebuilds it at runtime:
 *
 *   <IIFE charcode>   (function(){var A=Array.prototype.slice.call(arguments),
 *                      B=A.shift();return A.reverse().map(function(C,D){
 *                      return String.fromCharCode(C-B-<shift2>-D)}).join('')})
 *                      (<shift1>, code(n-1)+s1+s2+(n-1), …, code(0)+s1+s2+0)
 *   <R36 unit>        '0'+'…'+(parseInt-value).toString(36).toLowerCase()
 *                      (pieces ≤ 10 chars of [0-9a-z]; leading zeros kept as a
 *                      separate literal; control-range chars re-shifted by
 *                      .split('').map(c => String.fromCharCode(
 *                        c.charCodeAt()+(OFFSET))).join(''))
 *   parts joined with '+' (random-length, alternating encodings)
 *
 * and `T === 'str'` directives with a chain of `&&`-pieces in REVERSED order:
 *   (T).indexOf(code,i)===i  alternating  (new RegExp('^[^]{i}'+code)).test(T)
 *   ending in (T).length===len — sound for equality because the pieces cover
 *   [0,len) exactly.
 *
 * The pass folds all of that back to plain literals/comparisons. Every fold is
 * an exact static evaluation (pure arithmetic over literals), so it is safe
 * even if it ever matches non-gnirts code. Evaluation-count of a match target
 * drops back to one — the original `T === 'str'` semantics (gnirts evaluated
 * T up to three times per check).
 */

const require = (await import("module")).createRequire(import.meta.url);
const t = require("@babel/types");

const SKIP_KEYS = new Set([
  "loc", "start", "end", "range", "extra",
  "leadingComments", "trailingComments", "innerComments",
]);

function children(node) {
  const out = [];
  for (const key of Object.keys(node)) {
    if (SKIP_KEYS.has(key)) continue;
    const v = node[key];
    if (Array.isArray(v)) v.forEach((el, i) => { if (el && typeof el === "object") out.push([el, key, i]); });
    else if (v && typeof v === "object" && typeof v.type === "string") out.push([v, key, null]);
  }
  return out;
}

// -------------------------------------------------------------- checking

const isId = (n, name) => t.isIdentifier(n, { name });
const isStr = (n, value) => t.isStringLiteral(n, { value });
const isNum = (n, value) => t.isNumericLiteral(n, { value });

/** callee of the form obj.prop (non-computed) */
function memberCall(node, object, prop) {
  return t.isCallExpression(node) && t.isMemberExpression(node.callee) &&
    !node.callee.computed && t.isIdentifier(node.callee.property, { name: prop }) &&
    (object === undefined ? true : deepEq(node.callee.object, object));
}

/** structural equality ignoring source spans */
function deepEq(a, b) {
  if (a === b) return true;
  if (!a || !b || typeof a.type !== "string" || typeof b.type !== "string") return false;
  if (a.type !== b.type) return false;
  if (a.type === "Identifier") return a.name === b.name;
  if (a.type === "StringLiteral") return a.value === b.value;
  if (a.type === "NumericLiteral") return a.value === b.value;
  if (a.type === "BooleanLiteral") return a.value === b.value;
  if (a.type === "RegExpLiteral") return a.pattern === b.pattern && a.flags === b.flags;
  if (a.type === "NullLiteral") return true;
  const ka = Object.keys(a).filter((k) => !SKIP_KEYS.has(k) && k !== "type" && a[k] && typeof a[k] === "object");
  const kb = Object.keys(b).filter((k) => !SKIP_KEYS.has(k) && k !== "type" && b[k] && typeof b[k] === "object");
  if (ka.length !== kb.length) return false;
  for (const k of ka) {
    if (Array.isArray(a[k])) {
      if (!Array.isArray(b[k]) || a[k].length !== b[k].length) return false;
      for (let i = 0; i < a[k].length; i++) if (!deepEq(a[k][i], b[k][i])) return false;
    } else if (!deepEq(a[k], b[k])) return false;
  }
  return true;
}

/** static numeric value of a parenthesized/signed literal, else null */
function staticNumber(node) {
  if (t.isNumericLiteral(node)) return node.value;
  if (t.isUnaryExpression(node) && (node.operator === "-" || node.operator === "+")) {
    const v = staticNumber(node.argument);
    return v === null ? null : (node.operator === "-" ? -v : v);
  }
  return null;
}

// ------------------------------------------------------- string folding

/** fold one gnirts string-piece expression to its string value, else null */
function foldString(node) {
  if (!node) return null;

  // (NUM).toString(36).toLowerCase()  — R36 unit (the offset-shift variant
  // is a longer chain handled below; this shape ends at toLowerCase)
  if (t.isCallExpression(node) && t.isMemberExpression(node.callee) &&
    !node.callee.computed && isId(node.callee.property, "toLowerCase") &&
    node.arguments.length === 0) {
    const toStr = node.callee.object;
    if (memberCall(toStr, undefined, "toString") && toStr.arguments.length === 1 &&
      isNum(toStr.arguments[0], 36) && t.isNumericLiteral(toStr.callee.object)) {
      return toStr.callee.object.value.toString(36);
    }
  }

  // offset shift: (…unit…).split('').map(function(c){return
  //   String.fromCharCode(c.charCodeAt()+(OFFSET))}).join('')
  if (t.isCallExpression(node) && memberCall(node, undefined, "join") &&
    node.arguments.length === 1 && isStr(node.arguments[0], "")) {
    const map = node.callee.object;
    if (memberCall(map, undefined, "map") && map.arguments.length === 1) {
      const fn = map.arguments[0];
      if (t.isFunctionExpression(fn) && fn.params.length === 1 && t.isIdentifier(fn.params[0])) {
        const C = fn.params[0].name;
        const ret = fn.body.body.length === 1 && t.isReturnStatement(fn.body.body[0]) ? fn.body.body[0].argument : null;
        if (ret && memberCall(ret, undefined, "fromCharCode") && ret.arguments.length === 1) {
          const sum = ret.arguments[0];
          if (t.isBinaryExpression(sum, { operator: "+" })) {
            const cc = sum.left;
            if (memberCall(cc, undefined, "charCodeAt") && cc.arguments.length === 0 &&
              t.isMemberExpression(cc.callee) && !cc.callee.computed &&
              isId(cc.callee.object, C) && isId(cc.callee.property, "charCodeAt")) {
              const offset = staticNumber(sum.right);
              if (offset !== null) {
                const subject = map.callee.object;
                if (memberCall(subject, undefined, "split") && subject.arguments.length === 1 && isStr(subject.arguments[0], "")) {
                  const inner = foldString(subject.callee.object);
                  if (inner !== null) {
                    let out = "";
                    for (const ch of inner) out += String.fromCharCode(ch.charCodeAt(0) + offset);
                    return out;
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  // charcode IIFE
  if (t.isCallExpression(node) && t.isFunctionExpression(node.callee)) {
    const fn = node.callee;
    if (fn.params.length === 0 && fn.body.body.length === 2) {
      const [decl, ret] = fn.body.body;
      if (t.isVariableDeclaration(decl, { kind: "var" }) && decl.declarations.length === 2 &&
        t.isReturnStatement(ret)) {
        const [dArgs, dShift] = decl.declarations;
        if (t.isIdentifier(dArgs.id) && t.isIdentifier(dShift.id) &&
          memberCall(dArgs.init, undefined, "call") && dArgs.init.arguments.length === 1 &&
          isId(dArgs.init.arguments[0], "arguments") &&
          t.isMemberExpression(dArgs.init.callee.object) && !dArgs.init.callee.object.computed &&
          isId(dArgs.init.callee.object.property, "slice") &&
          t.isMemberExpression(dArgs.init.callee.object.object) &&
          isId(dArgs.init.callee.object.object.property, "prototype") &&
          isId(dArgs.init.callee.object.object.object, "Array") &&
          memberCall(dShift.init, dArgs.id, "shift") && dShift.init.arguments.length === 0) {
          // return A.reverse().map(function(C,D){…}).join('')
          const join = ret.argument;
          if (memberCall(join, undefined, "join") && join.arguments.length === 1 && isStr(join.arguments[0], "")) {
            const map = join.callee.object;
            if (memberCall(map, undefined, "map") && map.arguments.length === 1) {
              const mapFn = map.arguments[0];
              if (t.isFunctionExpression(mapFn) && mapFn.params.length === 2 &&
                t.isIdentifier(mapFn.params[0]) && t.isIdentifier(mapFn.params[1]) &&
                mapFn.body.body.length === 1 && t.isReturnStatement(mapFn.body.body[0])) {
                const rev = map.callee.object;
                if (memberCall(rev, dArgs.id, "reverse") && rev.arguments.length === 0) {
                  const fromCharCode = mapFn.body.body[0].argument;
                  if (memberCall(fromCharCode, undefined, "fromCharCode") && fromCharCode.arguments.length === 1) {
                    const sub = fromCharCode.arguments[0];
                    const operands = [];
                    const flat = (e) => {
                      if (t.isBinaryExpression(e, { operator: "-" })) { flat(e.left); operands.push(e.right); }
                      else operands.push(e);
                    };
                    flat(sub);
                    const [C, D] = mapFn.params.map((p) => p.name);
                    if (operands.length === 4 && isId(operands[0], C) && isId(operands[1], dShift.id.name) &&
                      isId(operands[3], D)) {
                      const shift2 = staticNumber(operands[2]);
                      if (shift2 !== null && node.arguments.length >= 2 &&
                        node.arguments.every((a) => t.isNumericLiteral(a))) {
                        const shift1 = node.arguments[0].value;
                        const n = node.arguments.length - 1;
                        // args are pushed a(n-1)…a(0) with a(k)=code(k)+s1+s2+k,
                        // then shifted and reversed — so char(i) = args[n-i]-s1-s2-i
                        let out = "";
                        for (let i = 0; i < n; i++) {
                          out += String.fromCharCode(node.arguments[n - i].value - shift1 - shift2 - i);
                        }
                        return out;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  // parts joined with '+' — operands are pieces or plain string literals
  // (leading-zero prefixes like '0'+(…) come through here)
  if (t.isBinaryExpression(node, { operator: "+" })) {
    const sub = (n) => (t.isStringLiteral(n) ? n.value : foldString(n));
    const l = sub(node.left);
    if (l !== null) {
      const r = sub(node.right);
      if (r !== null) return l + r;
    }
  }

  return null;
}

// -------------------------------------------------------- match folding

/**
 * Fold a reversed `&&` chain of match-pieces to { target, str }, else null.
 * Output order: [(T).length===len], then pieces in reverse forward order:
 * (T).indexOf(code,i)===i alternating (new RegExp('^[^]{i}'+code)).test(T).
 */
function foldMatchChain(node) {
  const pieces = [];
  for (let cur = node; ; ) {
    if (t.isLogicalExpression(cur, { operator: "&&" })) { pieces.unshift(cur.right); cur = cur.left; }
    else { pieces.unshift(cur); break; }
  }
  if (pieces.length < 3) return null;

  // last-emitted (first in source) piece is the length check
  const lenPiece = pieces[0];
  if (!(t.isBinaryExpression(lenPiece, { operator: "===" }) &&
    t.isMemberExpression(lenPiece.left) && !lenPiece.left.computed &&
    isId(lenPiece.left.property, "length") && isNum(lenPiece.right, lenPiece.right.value))) return null;
  const target = lenPiece.left.object;
  const len = lenPiece.right.value;

  // forward order = source pieces reversed
  const forward = pieces.slice(1).reverse();
  let str = "";
  let expectIndex = 0;
  for (let k = 0; k < forward.length; k++) {
    const piece = forward[k];
    if (k % 2 === 0) {
      // (T).indexOf(code, i) === i
      if (!(t.isBinaryExpression(piece, { operator: "===" }) &&
        memberCall(piece.left, undefined, "indexOf") && piece.left.arguments.length === 2 &&
        isNum(piece.left.arguments[1], expectIndex) && isNum(piece.right, expectIndex) &&
        deepEq(piece.left.callee.object, target))) return null;
      const s = foldString(piece.left.arguments[0]);
      if (s === null) return null;
      str += s;
      expectIndex += s.length;
    } else {
      // (new RegExp('^[^]{i}' + code)).test(T)
      if (!(memberCall(piece, undefined, "test") && piece.arguments.length === 1 &&
        deepEq(piece.arguments[0], target) && t.isNewExpression(piece.callee.object) &&
        t.isIdentifier(piece.callee.object.callee, { name: "RegExp" }) &&
        piece.callee.object.arguments.length === 1)) return null;
      const pattern = piece.callee.object.arguments[0];
      // flatten the '+' chain (left-assoc) — operand 0 must be the `^[^]{i}` prefix
      const ops = [];
      const flat = (e) => {
        if (t.isBinaryExpression(e, { operator: "+" })) { flat(e.left); ops.push(e.right); }
        else ops.push(e);
      };
      flat(pattern);
      if (ops.length < 2 || !isStr(ops[0], `^[^]{${expectIndex}}`)) return null;
      let s = "";
      for (const op of ops.slice(1)) {
        const v = t.isStringLiteral(op) ? op.value : foldString(op);
        if (v === null) return null;
        s += v;
      }
      // the RegExp source is escapePattern()'d: every \x00-\x7f char became a
      // \xNN escape — decode it back to the original characters
      if (s.includes("\\x")) {
        s = s.replace(/\\x([0-9a-fA-F]{2})/g, (m, h) => String.fromCharCode(parseInt(h, 16)));
      }
      str += s;
      expectIndex += s.length;
    }
  }
  if (str.length !== len || expectIndex !== len) return null;
  return { target, str };
}

// ------------------------------------------------------------------ walk

/** fold one node to a replacement node, else null */
function foldNode(node) {
  // !(T.indexOf(…)===0 && …) → T !== "str"
  if (t.isUnaryExpression(node, { operator: "!", prefix: true })) {
    const m = foldMatchChain(node.argument);
    if (m) return t.binaryExpression("!==", t.cloneNode(m.target, true), t.stringLiteral(m.str));
    return null;
  }
  // T.indexOf(…)===0 && … → T === "str"
  const m = foldMatchChain(node);
  if (m) return t.binaryExpression("===", t.cloneNode(m.target, true), t.stringLiteral(m.str));
  // string pieces → "str"
  const s = foldString(node);
  if (s !== null) return t.stringLiteral(s);
  return null;
}

/**
 * Fold every gnirts expression in the AST (top-down; folded nodes are not
 * re-entered). Returns the number of folds.
 */
export function unGnirts(ast) {
  let folded = 0;
  const rec = (node, assign) => {
    if (!node || typeof node.type !== "string") return;
    if (assign) {
      const replacement = foldNode(node);
      if (replacement) { assign(replacement); folded++; return; }
    }
    for (const [child, key, index] of children(node)) {
      rec(child, (nn) => {
        if (index === null) node[key] = nn;
        else node[key][index] = nn;
      });
    }
  };
  rec(ast.program, null);
  return folded;
}
