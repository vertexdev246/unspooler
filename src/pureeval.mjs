/**
 * Pure-subset evaluator: folds calls to helper functions whose results are
 * constants, WITHOUT running the input as code.
 *
 * It interprets a small JavaScript subset over values it creates itself:
 * primitives, fresh arrays / plain objects, and references to the input's own
 * function declarations (interpreted the same way). Only allow-listed pure
 * built-ins may be called (string / number / array helpers, Math.floor, …),
 * only on primitives or on values the evaluator created. No `this`, no
 * `new`, no getters/setters, no host objects, no property writes outside its
 * own values, no Function/eval (a `Function(text)` call yields a marker that
 * carries the text). Every run has a step budget. Anything outside the
 * subset throws Unsupported and the caller leaves the code alone.
 */
import { createRequire } from "module";
const require = createRequire(import.meta.url);
const t = require("@babel/types");

export class Unsupported extends Error {}

const SAFE = new Set();
const addProto = (proto, skip = []) => {
  for (const k of Object.getOwnPropertyNames(proto)) {
    if (k === "constructor" || skip.includes(k)) continue;
    const d = Object.getOwnPropertyDescriptor(proto, k);
    if (d && typeof d.value === "function") SAFE.add(d.value);
  }
};
addProto(String.prototype);
addProto(Number.prototype);
addProto(Boolean.prototype);
for (const k of ["concat", "join", "slice", "at", "indexOf", "lastIndexOf", "includes", "flat", "toString", "reverse", "fill", "push", "pop", "shift", "unshift", "splice", "keys", "values", "entries"])
  SAFE.add(Array.prototype[k]);
SAFE.add(Object.prototype.toString);
// pure base64 codecs, independent of Buffer/atob availability
const B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
const pureAtob = (s) => {
  s = String(s).replace(/[\t\n\f\r ]/g, "");
  if (s.length % 4 === 1) throw new Error("bad base64");
  s = s.replace(/=+$/, "");
  let out = "", bits = 0, n = 0;
  for (const ch of s) {
    const v = B64.indexOf(ch);
    if (v < 0) throw new Error("bad base64 char");
    bits = (bits << 6) | v; n += 6;
    if (n >= 8) { n -= 8; out += String.fromCharCode((bits >> n) & 0xff); }
  }
  return out;
};
const pureBtoa = (s) => {
  s = String(s); let out = "";
  for (let i = 0; i < s.length; i += 3) {
    const a = s.charCodeAt(i), b = s.charCodeAt(i + 1), c = s.charCodeAt(i + 2);
    if (a > 0xff || b > 0xff || c > 0xff) throw new Error("btoa range");
    out += B64[a >> 2] + B64[((a & 3) << 4) | (b >> 4 || 0)];
    out += i + 1 < s.length ? B64[((b & 15) << 2) | (c >> 6 || 0)] : "=";
    out += i + 2 < s.length ? B64[c & 63] : "=";
  }
  return out;
};
for (const f of [String, Number, Boolean, Array, parseInt, parseFloat, isNaN, isFinite, escape, unescape, encodeURI, encodeURIComponent,
  decodeURI, decodeURIComponent, String.fromCharCode, String.fromCodePoint, Math.floor, Math.ceil, Math.round, Math.abs, Math.max,
  Math.min, Math.pow, Math.trunc, Math.sign, Number.parseInt, Number.parseFloat, Number.isNaN, Number.isInteger, pureAtob, pureBtoa])
  SAFE.add(f);
// every built-in method of the primitive / array prototypes: readable, not necessarily callable
const NATIVE = new Set();
for (const proto of [Array.prototype, String.prototype, Number.prototype, Boolean.prototype, Object.prototype])
  for (const k of Object.getOwnPropertyNames(proto)) { const d = Object.getOwnPropertyDescriptor(proto, k); if (d && typeof d.value === "function" && k !== "constructor") NATIVE.add(d.value); }
const GLOBALS = new Map([
  ["String", String], ["Number", Number], ["Boolean", Boolean], ["parseInt", parseInt], ["parseFloat", parseFloat],
  ["isNaN", isNaN], ["isFinite", isFinite], ["escape", escape], ["unescape", unescape], ["encodeURI", encodeURI],
  ["encodeURIComponent", encodeURIComponent], ["decodeURI", decodeURI], ["decodeURIComponent", decodeURIComponent],
  ["Math", Math], ["undefined", undefined], ["NaN", NaN], ["Infinity", Infinity], ["atob", pureAtob], ["btoa", pureBtoa],
]);
const BLOCKED = new Set(["__proto__", "prototype", "constructor", "caller", "arguments", "callee", "__defineGetter__", "__defineSetter__", "__lookupGetter__", "__lookupSetter__"]);

const FUNC = Object.freeze({ marker: "Function constructor" });

export class FunctionText {
  constructor(params, body) { this.params = params; this.body = body; }
}

class Closure {
  constructor(node, path, env) { this.node = node; this.path = path; this.env = env; }
}
const BREAK = { k: "break" }, CONTINUE = { k: "continue" };

/**
 * @param resolveFn (name, scopePath) -> {node, path} for a FunctionDeclaration /
 *                  function value the identifier is bound to, or null
 * @param resolveMember (objectName, prop) -> {node, path} or null
 */
export function makeEvaluator({ resolveFn, resolveMember, resolveConst = null, budget = 2_000_000 }) {
  const own = new WeakSet();
  let steps = 0;
  const tick = () => { if (++steps > budget) throw new Unsupported("step budget exhausted"); };
  const mine = (v) => { if (v && typeof v === "object") own.add(v); return v; };
  const okVal = (v) => v === null || (typeof v !== "object" && typeof v !== "function") || own.has(v) || v instanceof Closure;
  const okArg = (v) => v === null || (typeof v !== "object" && typeof v !== "function") || own.has(v);

  class Env {
    constructor(parent, fnPath) { this.vars = new Map(); this.parent = parent; this.fnPath = fnPath ?? parent?.fnPath ?? null; }
    lookup(name) { for (let e = this; e; e = e.parent) if (e.vars.has(name)) return e; return null; }
  }

  function getProp(obj, key) {
    tick();
    if (obj === null || obj === undefined) throw new Unsupported("property of " + obj);
    if (obj instanceof Closure || obj instanceof FunctionText) throw new Unsupported("property of a function");
    if (obj === Math) {
      const v = Math[key];
      if (typeof v === "number" || SAFE.has(v)) return v;
      throw new Unsupported("Math." + key);
    }
    if (typeof obj === "function") {
      if (obj === String && (key === "fromCharCode" || key === "fromCodePoint")) return String[key];
      throw new Unsupported("property of a built-in");
    }
    const k = typeof key === "symbol" ? key : String(key);
    if (k === "constructor") {
      // JSFuck idiom: reach the primitive constructors (and Function, which stays a marker)
      if (typeof obj === "string") return String;
      if (typeof obj === "number") return Number;
      if (typeof obj === "boolean") return Boolean;
      if (Array.isArray(obj) && own.has(obj)) return Array;
      if (typeof obj === "function" && SAFE.has(obj)) return FUNC;
      throw new Unsupported("constructor of a foreign value");
    }
    if (BLOCKED.has(k)) throw new Unsupported("blocked property " + k);
    if (typeof obj === "object" && !own.has(obj)) throw new Unsupported("foreign object");
    const v = obj[k];
    // a native built-in may be READ (e.g. coerced to its fixed source text); calls stay allow-listed
    if (typeof v === "function" && !SAFE.has(v) && !NATIVE.has(v)) throw new Unsupported("non-allow-listed method " + k);
    if (v && typeof v === "object" && !own.has(v)) throw new Unsupported("foreign object value");
    return v;
  }

  function callValue(fn, thisv, args, depth) {
    tick();
    if (fn instanceof Closure) return invoke(fn, args, depth + 1);
    if (fn === FUNC) {
      const strs = args.map((a) => String(a));
      return new FunctionText(strs.slice(0, -1), strs.length ? strs[strs.length - 1] : "");
    }
    if (typeof fn !== "function" || !SAFE.has(fn)) throw new Unsupported("call to a non-allow-listed function");
    if (!(thisv === undefined || okArg(thisv) || thisv === Math || fn === String.fromCharCode || fn === String.fromCodePoint)) throw new Unsupported("call on a foreign receiver");
    for (const a of args) if (!okArg(a)) throw new Unsupported("non-primitive argument");
    return big(mine(Reflect.apply(fn, thisv, args)));
  }

  function invoke(cl, args, depth) {
    if (depth > 200) throw new Unsupported("recursion");
    const node = cl.node;
    if (node.async || node.generator) throw new Unsupported("async/generator");
    const env = new Env(cl.env, cl.path);
    node.params.forEach((p, i) => {
      if (t.isIdentifier(p)) env.vars.set(p.name, { v: args[i], c: false });
      else if (t.isAssignmentPattern(p) && t.isIdentifier(p.left)) env.vars.set(p.left.name, { v: args[i] === undefined ? expr(p.right, env, depth) : args[i], c: false });
      else throw new Unsupported("parameter pattern");
    });
    if (!t.isArrowFunctionExpression(node)) env.vars.set("arguments", { v: undefined, c: true, banned: true });
    if (t.isArrowFunctionExpression(node) && !t.isBlockStatement(node.body)) return expr(node.body, env, depth);
    hoist(node.body.body, env);
    const r = block(node.body.body, env, depth);
    return r && r.k === "return" ? r.v : undefined;
  }

  function hoist(stmts, env) {
    for (const s of stmts) if (t.isFunctionDeclaration(s)) env.vars.set(s.id.name, { v: new Closure(s, null, env), c: false });
    // `var` is function-scoped wherever it appears (blocks, loops, switch cases) — not inside nested functions
    const walk = (n) => {
      if (!n || typeof n !== "object") return;
      if (Array.isArray(n)) return n.forEach(walk);
      if (t.isFunction(n)) return;
      if (t.isVariableDeclaration(n, { kind: "var" })) for (const d of n.declarations) if (t.isIdentifier(d.id) && !env.vars.has(d.id.name)) env.vars.set(d.id.name, { v: undefined, c: false });
      for (const k of t.VISITOR_KEYS[n.type] || []) walk(n[k]);
    };
    walk(stmts);
  }

  function block(stmts, env, depth) {
    for (const s of stmts) {
      const r = stmt(s, env, depth);
      if (r) return r;
    }
    return null;
  }

  /** what a loop does with a body result: "next" | "break" | "return" (propagate) */
  function loopCtl(r, label) {
    if (!r) return "next";
    if (r === CONTINUE || (r.k === "continue" && r.label === label)) return "next";
    if (r === BREAK || (r.k === "break" && r.label === label)) return "break";
    return "return";
  }
  function stmt(s, env, depth, label) {
    tick();
    switch (s.type) {
      case "ExpressionStatement": expr(s.expression, env, depth); return null;
      case "VariableDeclaration":
        for (const d of s.declarations) {
          if (!t.isIdentifier(d.id)) throw new Unsupported("destructuring");
          const v = d.init ? expr(d.init, env, depth) : undefined;
          if (s.kind === "var") { const e = env.lookup(d.id.name) || env; if (d.init) e.vars.get(d.id.name) ? (e.vars.get(d.id.name).v = v) : e.vars.set(d.id.name, { v, c: false }); else if (!e.vars.has(d.id.name)) e.vars.set(d.id.name, { v: undefined, c: false }); }
          else env.vars.set(d.id.name, { v, c: s.kind === "const" });
        }
        return null;
      case "ReturnStatement": return { k: "return", v: s.argument ? expr(s.argument, env, depth) : undefined };
      case "BlockStatement": { const e = new Env(env, env.fnPath); hoistLexical(s.body, e); return block(s.body, e, depth); }
      case "IfStatement": return expr(s.test, env, depth) ? stmt(s.consequent, env, depth) : s.alternate ? stmt(s.alternate, env, depth) : null;
      case "EmptyStatement": return null;
      case "FunctionDeclaration": return null; // hoisted
      case "BreakStatement": return s.label ? { k: "break", label: s.label.name } : BREAK;
      case "ContinueStatement": return s.label ? { k: "continue", label: s.label.name } : CONTINUE;
      case "LabeledStatement": {
        const loop = t.isWhileStatement(s.body) || t.isForStatement(s.body) || t.isDoWhileStatement(s.body);
        const r = loop ? stmt(s.body, env, depth, s.label.name) : stmt(s.body, env, depth);
        return r && r.k === "break" && r.label === s.label.name ? null : r;
      }
      case "WhileStatement":
        while (expr(s.test, env, depth)) {
          const r = stmt(s.body, env, depth);
          const c = loopCtl(r, label);
          if (c === "break") break;
          if (c === "return") return r;
        }
        return null;
      case "ForStatement": {
        const e = new Env(env, env.fnPath);
        if (s.init) t.isVariableDeclaration(s.init) ? stmt(s.init, e, depth) : expr(s.init, e, depth);
        if (s.init && t.isVariableDeclaration(s.init) && s.init.kind !== "var") throw new Unsupported("per-iteration let");
        for (; !s.test || expr(s.test, e, depth); s.update && expr(s.update, e, depth)) {
          const r = stmt(s.body, e, depth);
          const c = loopCtl(r, label);
          if (c === "break") break;
          if (c === "return") return r;
        }
        return null;
      }
      case "SwitchStatement": {
        const d = expr(s.discriminant, env, depth);
        const e = new Env(env, env.fnPath);
        let i = s.cases.findIndex((c) => c.test && expr(c.test, e, depth) === d);
        if (i < 0) i = s.cases.findIndex((c) => !c.test);
        if (i < 0) return null;
        for (; i < s.cases.length; i++) {
          const r = block(s.cases[i].consequent, e, depth);
          if (r === BREAK) return null;
          if (r) return r;
        }
        return null;
      }
      default: throw new Unsupported("statement " + s.type);
    }
  }
  function hoistLexical(stmts, env) {
    for (const s of stmts) if (t.isFunctionDeclaration(s)) env.vars.set(s.id.name, { v: new Closure(s, null, env), c: false });
  }

  function lookupName(name, env, depth) {
    const e = env.lookup(name);
    if (e) {
      const slot = e.vars.get(name);
      if (slot.banned) throw new Unsupported("arguments");
      return slot.v;
    }
    const f = resolveFn(name, env.fnPath);
    if (f) return new Closure(f.node, f.path, null);
    // outer constants the caller has proven (e.g. a decoded string table): a fresh copy each time
    const c = resolveConst && resolveConst(name, env.fnPath);
    if (c) return Array.isArray(c.v) ? mine(c.v.slice()) : c.v;
    if (name === "Function") return FUNC;
    if (GLOBALS.has(name)) return GLOBALS.get(name);
    throw new Unsupported("free name " + name);
  }
  function assignName(name, v, env) {
    const e = env.lookup(name);
    if (!e) throw new Unsupported("write to an outer/global name " + name);
    const slot = e.vars.get(name);
    if (slot.c || slot.banned) throw new Unsupported("write to const");
    slot.v = v;
  }

  // values this large are not constants anyone wants inlined (and doubling loops would exhaust memory)
  const big = (v) => { if ((typeof v === "string" || Array.isArray(v)) && v.length > 1_000_000) throw new Unsupported("value too large"); return v; };
  const BIN = {
    "+": (a, b) => a + b, "-": (a, b) => a - b, "*": (a, b) => a * b, "/": (a, b) => a / b, "%": (a, b) => a % b,
    "**": (a, b) => a ** b, "&": (a, b) => a & b, "|": (a, b) => a | b, "^": (a, b) => a ^ b, "<<": (a, b) => a << b,
    ">>": (a, b) => a >> b, ">>>": (a, b) => a >>> b, "==": (a, b) => a == b, "!=": (a, b) => a != b, // eslint-disable-line eqeqeq
    "===": (a, b) => a === b, "!==": (a, b) => a !== b, "<": (a, b) => a < b, "<=": (a, b) => a <= b, ">": (a, b) => a > b, ">=": (a, b) => a >= b,
  };
  // operators coerce objects via valueOf/toString: only own arrays / primitives may be operands
  // a built-in function coerces to its fixed source text ("function flat() { [native code] }"): allowed
  const opnd = (v) => { if (typeof v === "function" && (SAFE.has(v) || NATIVE.has(v))) return v; if (v instanceof Closure || v instanceof FunctionText || (v && typeof v === "object" && !own.has(v)) || typeof v === "function" || v === FUNC) throw new Unsupported("operator on a function/foreign value"); if (v && typeof v === "object" && !Array.isArray(v) && !isBuiltinIterator(v)) throw new Unsupported("operator on a plain object"); return v; };
  // a fresh built-in iterator with no own properties coerces to "[object Array Iterator]" etc. — no user code runs
  const isBuiltinIterator = (v) => own.has(v) && Reflect.ownKeys(v).length === 0 && /^\[object (Array|String) Iterator\]$/.test(Object.prototype.toString.call(v));

  function expr(n, env, depth) {
    tick();
    switch (n.type) {
      case "NumericLiteral": case "StringLiteral": case "BooleanLiteral": return n.value;
      case "NullLiteral": return null;
      case "Identifier": return lookupName(n.name, env, depth);
      case "TemplateLiteral": {
        let s = n.quasis[0].value.cooked;
        n.expressions.forEach((e, i) => { s += String(opnd(expr(e, env, depth))) + n.quasis[i + 1].value.cooked; });
        return s;
      }
      case "ArrayExpression": return mine(n.elements.map((e) => { if (!e || t.isSpreadElement(e)) throw new Unsupported("holes/spread"); return expr(e, env, depth); }));
      case "ObjectExpression": {
        const o = mine({});
        for (const p of n.properties) {
          if (!t.isObjectProperty(p) || p.computed) throw new Unsupported("object literal shape");
          const k = t.isIdentifier(p.key) ? p.key.name : String(p.key.value);
          if (BLOCKED.has(k)) throw new Unsupported("blocked key");
          Object.defineProperty(o, k, { value: expr(p.value, env, depth), writable: true, enumerable: true, configurable: true });
        }
        return o;
      }
      case "ParenthesizedExpression": return expr(n.expression, env, depth);
      case "SequenceExpression": { let v; for (const e of n.expressions) v = expr(e, env, depth); return v; }
      case "UnaryExpression": {
        if (n.operator === "typeof" && t.isIdentifier(n.argument)) {
          try { return typeOf(lookupName(n.argument.name, env, depth)); } catch (e) { if (e instanceof Unsupported) throw e; throw e; }
        }
        const v = expr(n.argument, env, depth);
        switch (n.operator) {
          case "!": return !v;
          case "+": return +opnd(v);
          case "-": return -opnd(v);
          case "~": return ~opnd(v);
          case "void": return undefined;
          case "typeof": return typeOf(v);
        }
        throw new Unsupported("unary " + n.operator);
      }
      case "BinaryExpression": {
        if (n.operator === "in" || n.operator === "instanceof") throw new Unsupported(n.operator);
        const a = opnd(expr(n.left, env, depth)), b = opnd(expr(n.right, env, depth));
        return big(BIN[n.operator](a, b));
      }
      case "LogicalExpression": {
        const a = expr(n.left, env, depth);
        if (n.operator === "&&") return a ? expr(n.right, env, depth) : a;
        if (n.operator === "||") return a ? a : expr(n.right, env, depth);
        return a ?? expr(n.right, env, depth);
      }
      case "ConditionalExpression": return expr(n.test, env, depth) ? expr(n.consequent, env, depth) : expr(n.alternate, env, depth);
      case "MemberExpression": {
        const o = expr(n.object, env, depth);
        const k = n.computed ? opnd(expr(n.property, env, depth)) : n.property.name;
        if (!n.computed && t.isIdentifier(n.object) && typeof o === "object" && o !== null && !own.has(o) && o !== Math) throw new Unsupported("foreign object");
        return getProp(o, k);
      }
      case "CallExpression": {
        let fn, thisv;
        if (t.isMemberExpression(n.callee)) {
          // own-member helper functions (e.g. RUNTIME.name = function(){…})
          if (!n.callee.computed && t.isIdentifier(n.callee.object) && !env.lookup(n.callee.object.name) && resolveMember) {
            const m = resolveMember(n.callee.object.name, n.callee.property.name);
            if (m) return invoke(new Closure(m.node, m.path, null), n.arguments.map((a) => argVal(a, env, depth)), depth);
          }
          thisv = expr(n.callee.object, env, depth);
          fn = getProp(thisv, n.callee.computed ? opnd(expr(n.callee.property, env, depth)) : n.callee.property.name);
        } else { fn = expr(n.callee, env, depth); thisv = undefined; }
        const args = n.arguments.map((a) => argVal(a, env, depth));
        return callValue(fn, thisv, args, depth);
      }
      case "AssignmentExpression": {
        const v = n.operator === "=" ? expr(n.right, env, depth) : big(BIN[n.operator.slice(0, -1)](opnd(readTarget(n.left, env, depth)), opnd(expr(n.right, env, depth))));
        writeTarget(n.left, v, env, depth);
        return v;
      }
      case "UpdateExpression": {
        if (t.isIdentifier(n.argument)) {
          const old = +opnd(lookupName(n.argument.name, env, depth));
          assignName(n.argument.name, n.operator === "++" ? old + 1 : old - 1, env);
          return n.prefix ? (n.operator === "++" ? old + 1 : old - 1) : old;
        }
        if (t.isMemberExpression(n.argument)) {
          const o = expr(n.argument.object, env, depth);
          if (!own.has(o)) throw new Unsupported("update on foreign object");
          const k = n.argument.computed ? opnd(expr(n.argument.property, env, depth)) : n.argument.property.name;
          const old = +opnd(getProp(o, k));
          const nv = n.operator === "++" ? old + 1 : old - 1;
          setOwn(o, k, nv);
          return n.prefix ? nv : old;
        }
        throw new Unsupported("update target");
      }
      case "FunctionExpression": case "ArrowFunctionExpression": return new Closure(n, null, env);
      default: throw new Unsupported("expression " + n.type);
    }
  }
  function argVal(a, env, depth) { if (t.isSpreadElement(a)) throw new Unsupported("spread argument"); return expr(a, env, depth); }
  function typeOf(v) { if (v instanceof Closure) return "function"; if (v instanceof FunctionText) throw new Unsupported("typeof Function text"); return typeof v; }
  function readTarget(l, env, depth) {
    if (t.isIdentifier(l)) return lookupName(l.name, env, depth);
    if (t.isMemberExpression(l)) { const o = expr(l.object, env, depth); return getProp(o, l.computed ? opnd(expr(l.property, env, depth)) : l.property.name); }
    throw new Unsupported("assignment target");
  }
  function setOwn(o, k, v) {
    if (!own.has(o)) throw new Unsupported("write to a foreign object");
    const key = String(k);
    if (BLOCKED.has(key)) throw new Unsupported("blocked key");
    if (Array.isArray(o) && key === "length") { o.length = v; return; }
    Object.defineProperty(o, key, { value: v, writable: true, enumerable: true, configurable: true });
  }
  function writeTarget(l, v, env, depth) {
    if (t.isIdentifier(l)) return assignName(l.name, v, env);
    if (t.isMemberExpression(l)) {
      const o = expr(l.object, env, depth);
      return setOwn(o, l.computed ? opnd(expr(l.property, env, depth)) : l.property.name, v);
    }
    throw new Unsupported("assignment target");
  }

  return {
    /** evaluate a call to function `fn` ({node, path}) with constant args; returns a primitive or FunctionText */
    call(fn, args) {
      steps = 0;
      const v = invoke(new Closure(fn.node, fn.path, null), args, 0);
      if (v instanceof FunctionText) return v;
      if (v === null || (typeof v !== "object" && typeof v !== "function")) return v;
      throw new Unsupported("non-primitive result");
    },
    /** evaluate a standalone expression in the scope of `path` */
    expr(node, path) {
      steps = 0;
      const v = expr(node, new Env(null, path), 0);
      if (v instanceof FunctionText) return v;
      if (v === null || (typeof v !== "object" && typeof v !== "function")) return v;
      throw new Unsupported("non-primitive result");
    },
  };
}
