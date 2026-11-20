/**
 * JSFuck reverser — exact, and without executing the input.
 *
 * JSFuck programs use only []()!+ . They build every character from
 * coercions ("false"[0] === "f"), stitch strings together, reach the Function
 * constructor through []["filter"]["constructor"], and finally run
 *     Function("<program text>")()
 *
 * This module parses that six-character language itself (Babel's recursive
 * walks overflow on real JSFuck: a 1 KB program is ~1 MB of nested `+`) and
 * evaluates it with a deliberately tiny value model:
 *
 *  - primitives behave as in JavaScript;
 *  - only built-ins on an allow-list may be *called* (pure string / number /
 *    array helpers, escape, unescape, String.fromCharCode, Date, …), and only
 *    on primitives or on values this evaluator created itself;
 *  - Function(...) is never compiled: it becomes a marker holding the source
 *    text. Calling it yields the recovered program, which is printed, not run.
 *    The few tiny bodies JSFuck uses to reach globals ("return escape",
 *    "return/0/", "return new Date(200000000)", "return this") are recognised
 *    by exact match.
 *
 * Results are those of a V8 engine (Node / Chrome), the same strings the
 * JSFuck encoder relies on (e.g. "function filter() { [native code] }").
 */

class Unsupported extends Error {}

/* ---------------- markers ---------------- */
const NATIVE_FUNCTION_TEXT = String(Function); // "function Function() { [native code] }"
const FUNC = { kind: "Function", [Symbol.toPrimitive]: () => NATIVE_FUNCTION_TEXT };
const GLOBAL = { kind: "global", [Symbol.toPrimitive]: () => "[object global]" };
const EVAL = { kind: "eval", [Symbol.toPrimitive]: () => "function eval() { [native code] }" };
class Compiled {
  constructor(params, body) { this.params = params; this.body = body; }
  [Symbol.toPrimitive]() { return `function anonymous(${this.params.join(",")}\n) {\n${this.body}\n}`; }
}
class Payload {
  constructor(kind, code, params = [], args = []) { this.kind = kind; this.code = code; this.params = params; this.args = args; }
  [Symbol.toPrimitive]() { throw new Unsupported("payload result used as a value"); }
}
const isMarker = (v) => v === FUNC || v === GLOBAL || v === EVAL || v instanceof Compiled || v instanceof Payload;

/* ---------------- what may be called ---------------- */
const SAFE = new Set();
const addAll = (proto, skip = []) => {
  for (const k of Object.getOwnPropertyNames(proto)) {
    if (k === "constructor" || skip.includes(k)) continue;
    const d = Object.getOwnPropertyDescriptor(proto, k);
    if (d && typeof d.value === "function") SAFE.add(d.value);
  }
};
addAll(String.prototype);
addAll(Number.prototype);
addAll(Boolean.prototype);
addAll(RegExp.prototype, ["compile"]);
addAll(Date.prototype);
for (const k of ["concat", "join", "slice", "at", "indexOf", "lastIndexOf", "includes", "flat", "toString", "toLocaleString",
  "entries", "keys", "values", "reverse", "fill", "push", "pop", "shift", "unshift", "splice", "sort"])
  SAFE.add(Array.prototype[k]);
SAFE.add(Object.prototype.toString);
SAFE.add(Object.prototype.valueOf);
for (const f of [String, Number, Boolean, Array, RegExp, Date, escape, unescape, encodeURI, encodeURIComponent, decodeURI,
  decodeURIComponent, parseInt, parseFloat, isNaN, isFinite, String.fromCharCode, String.fromCodePoint, String.raw,
  Number.parseInt, Number.parseFloat, Number.isNaN, Number.isFinite, Number.isInteger, Array.of, Array.isArray])
  SAFE.add(f);
const BLOCKED_KEYS = new Set(["__proto__", "prototype", "caller", "arguments", "callee", "__defineGetter__", "__defineSetter__", "__lookupGetter__", "__lookupSetter__"]);

// tiny Function bodies the JSFuck alphabet uses to reach globals
const GLOBAL_BODIES = new Map([
  ["escape", escape], ["unescape", unescape], ["Date", Date], ["String", String], ["Number", Number], ["Boolean", Boolean],
  ["Array", Array], ["RegExp", RegExp], ["parseInt", parseInt], ["parseFloat", parseFloat], ["isNaN", isNaN],
  ["encodeURI", encodeURI], ["encodeURIComponent", encodeURIComponent], ["decodeURI", decodeURI], ["decodeURIComponent", decodeURIComponent],
]);

export function evaluateJsfuck(src) {
  const own = new WeakSet(); // objects this evaluator created
  const mark = (v) => { if (v && typeof v === "object" && !isMarker(v)) own.add(v); return v; };
  const okArg = (v) => v === null || (typeof v !== "object" && typeof v !== "function") || own.has(v);
  const okRecv = (v) => v === undefined || okArg(v) || SAFE.has(v);
  let i = 0;
  const n = src.length;
  const ws = () => { while (i < n && (src[i] === " " || src[i] === "\n" || src[i] === "\r" || src[i] === "\t")) i++; };
  const peek = () => (ws(), src[i]);
  const expect = (c) => { if (peek() !== c) throw new Unsupported(`expected ${c} at ${i}`); i++; };

  function getProp(obj, key) {
    if (obj === null || obj === undefined) throw new Unsupported("property of " + obj);
    if (obj instanceof Compiled || obj instanceof Payload || obj === EVAL) throw new Unsupported("property of a compiled function");
    const k = typeof key === "symbol" ? key : String(key);
    if (BLOCKED_KEYS.has(k)) throw new Unsupported("blocked property " + k);
    const target = obj === FUNC ? Function : obj === GLOBAL ? null : obj;
    if (target === null) throw new Unsupported("global property access");
    const v = target[k];
    if (v === Function) return FUNC;
    if (typeof v === "function" && (v.name === "eval" || v === globalThis.eval)) return EVAL;
    return v;
  }
  function call(fn, recv, args) {
    if (fn === FUNC) {
      const strs = args.map((a) => String(a));
      return new Compiled(strs.slice(0, -1), strs.length ? strs[strs.length - 1] : "");
    }
    if (fn === EVAL) {
      if (!args.length) return undefined;
      if (typeof args[0] !== "string") return args[0];
      return new Payload("eval", args[0]);
    }
    if (fn instanceof Compiled) {
      const body = fn.body.trim().replace(/;$/, "").trim();
      let m;
      if (!fn.params.length) {
        if ((m = /^return\s*([A-Za-z]+)$/.exec(body))) {
          if (m[1] === "this") return GLOBAL;
          if (m[1] === "eval") return EVAL;
          if (GLOBAL_BODIES.has(m[1])) return GLOBAL_BODIES.get(m[1]);
        }
        if ((m = /^return\s*\/([^/\n]*)\/([a-z]*)$/.exec(body))) return mark(new RegExp(m[1], m[2]));
        if ((m = /^return\s+new\s+Date\(\s*(\d+)\s*\)$/.exec(body))) return mark(new Date(+m[1]));
      }
      for (const a of args) if (!okArg(a) || (a && typeof a === "object")) throw new Unsupported("non-primitive argument to compiled code");
      return new Payload("function", fn.body, fn.params, args);
    }
    if (typeof fn !== "function" || !SAFE.has(fn)) throw new Unsupported("call to a function outside the allow-list");
    if (!okRecv(recv)) throw new Unsupported("call on a foreign object");
    for (const a of args) if (!okArg(a)) throw new Unsupported("non-primitive argument");
    return mark(Reflect.apply(fn, recv, args));
  }
  const plus = (a, b) => {
    if (a instanceof Payload || b instanceof Payload) throw new Unsupported("payload result used as a value");
    return a + b;
  };

  // expr := unary ('+' unary)*     (left-associative, iterative)
  function expr() {
    let v = unary();
    while (peek() === "+") { i++; v = plus(v, unary()); }
    return v;
  }
  // unary := ('!' | '+')* postfix  (applied right to left)
  function unary() {
    const ops = [];
    for (let c = peek(); c === "!" || c === "+"; c = peek()) { ops.push(c); i++; }
    let v = postfix();
    for (let k = ops.length - 1; k >= 0; k--) {
      if (v instanceof Payload) throw new Unsupported("payload result used as a value");
      v = ops[k] === "!" ? !v : +v;
    }
    return v;
  }
  // postfix := primary ( '[' expr ']' | '(' args ')' )*
  function postfix() {
    let v = primary(), recv;
    for (;;) {
      const c = peek();
      if (c === "[") { i++; const k = expr(); expect("]"); recv = v; v = getProp(v, k); }
      else if (c === "(") {
        i++; const args = [];
        if (peek() !== ")") { args.push(expr()); while (peek() === ",") { i++; args.push(expr()); } }
        expect(")"); v = call(v, recv, args); recv = undefined;
      } else return v;
    }
  }
  // primary := '[' elements ']' | '(' expr ')'
  function primary() {
    const c = peek();
    if (c === "[") {
      i++; const arr = [];
      if (peek() !== "]") { arr.push(expr()); while (peek() === ",") { i++; arr.push(expr()); } }
      expect("]");
      for (const a of arr) if (isMarker(a)) throw new Unsupported("marker inside an array");
      return mark(arr);
    }
    if (c === "(") { i++; const v = expr(); expect(")"); return v; }
    throw new Unsupported(`unexpected ${JSON.stringify(c)} at ${i}`);
  }

  const results = [];
  while (peek() !== undefined) {
    results.push(expr());
    while (peek() === ";") i++;
  }
  return results;
}

/** Only the six JSFuck characters (plus whitespace / ; separators). */
export function isJsfuck(code) {
  const body = code.replace(/\s+/g, "");
  return body.length >= 20 && /^[[\]()!+;]+$/.test(body);
}

function literal(v) {
  if (typeof v === "string") return JSON.stringify(v);
  if (typeof v === "number") return Object.is(v, -0) ? "-0" : String(v);
  if (typeof v === "boolean" || v === null) return String(v);
  if (v === undefined) return "void 0";
  if (typeof v === "bigint") return v + "n";
  return null;
}

/**
 * @param code      whole-file JSFuck
 * @param canUnwrap (body) => boolean — true when `body` may run at top level
 *                  instead of inside a function (no declarations / return /
 *                  this / arguments at its top level)
 * @returns {code, payloads} or {error}
 */
export function unJsfuck(code, canUnwrap) {
  let results;
  try {
    results = evaluateJsfuck(code);
  } catch (e) {
    if (e instanceof Unsupported) return { error: e.message };
    return { error: String(e && e.message || e) };
  }
  const out = [];
  let payloads = 0;
  for (const v of results) {
    if (v instanceof Payload) {
      payloads++;
      if (v.kind === "eval") out.push(v.code); // indirect eval runs in global scope: inline as-is
      else if (!v.params.length && !v.args.length && canUnwrap(v.code)) out.push(v.code);
      else {
        const args = v.args.map(literal);
        if (args.some((a) => a === null)) return { error: "payload called with a non-literal argument" };
        out.push(`(function (${v.params.join(", ")}) {\n${v.code}\n})(${args.join(", ")});`);
      }
    } else {
      const lit = literal(v);
      if (lit === null) return { error: "expression evaluates to an object; nothing to print" };
      out.push(lit + ";");
    }
  }
  return { code: out.join("\n"), payloads };
}
