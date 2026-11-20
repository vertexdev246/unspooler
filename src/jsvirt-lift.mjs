/**
 * js-virtualizer bytecode -> JavaScript lifter.
 *
 * Exactness first: every instruction is translated to JS with the VM's own
 * semantics (registers are plain local variables of the function; the VM
 * gives each call its own register file, so they never escape). Readability
 * comes from three conservative rewrites:
 *   1. block-local constant propagation (the compiler's index/counter regs),
 *   2. inlining a temporary into its single use when evaluation order is
 *      provably unchanged (side-effecting operations keep their order),
 *   3. control-flow recovery for the shapes this compiler emits (if/else,
 *      loops, break/continue); anything else is refused, not guessed.
 *
 * Unsupported opcodes (VFUNC_*, TRY_CATCH_FINALLY, WRITE_EXT, reserved
 * register writes) throw LiftError and the caller keeps the original wrapper.
 */
import { FORMATS } from "./jsvirt.mjs";

export class LiftError extends Error {}

const IP = 0, UNDEF = 1, VOIDR = 2;
const BINOPS = {
  EQ_COERCE: "==", EQ: "===", NOT_EQ_COERCE: "!=", NOT_EQ: "!==", LESS_THAN: "<", LESS_THAN_EQ: "<=", GREATER_THAN: ">",
  GREATER_THAN_EQ: ">=", ADD: "+", SUBTRACT: "-", MULTIPLY: "*", DIVIDE: "/", MODULO: "%", AND: "&", OR: "|", XOR: "^",
  SHIFT_LEFT: "<<", SHIFT_RIGHT: ">>",
};
const PURE_BIN = new Set(["===", "!=="]); // never call user code
const UNOPS = { BNOT: "~", NOT: "!", NEGATE: "-", PLUS: "+", TYPEOF: "typeof " };
const PURE_UN = new Set(["NOT", "TYPEOF", "TEST", "TEST_NEQ", "VOID", "DELETE"]);
const UNSUPPORTED = new Set(["VFUNC_CALL", "VFUNC_SETUP_CALLBACK", "VFUNC_RETURN", "TRY_CATCH_FINALLY", "WRITE_EXT"]);
const TERMINATORS = new Set(["JUMP_UNCONDITIONAL", "JUMP_EQ", "JUMP_NOT_EQ", "THROW", "THROW_ARGUMENT", "END"]);

const isIdent = (s) => /^[A-Za-z_$][\w$]*$/.test(s) && !RESERVED.has(s);
const RESERVED = new Set("break case catch class const continue debugger default delete do else export extends finally for function if import in instanceof new return super switch this throw try typeof var void while with yield let static enum await implements package protected interface private public null true false".split(" "));
const lit = (v) => {
  if (v === undefined) return "void 0";
  if (typeof v === "string") return JSON.stringify(v);
  if (typeof v === "number") return Object.is(v, -0) ? "-0" : Number.isNaN(v) ? "NaN" : v === Infinity ? "Infinity" : v === -Infinity ? "-Infinity" : String(v);
  return String(v); // boolean / null
};
const isPrim = (v) => v === null || v === undefined || ["string", "number", "boolean"].includes(typeof v);

/** registers read / written by one instruction, in VM read order */
function regIO(ins) {
  const a = ins.args, op = ins.op;
  const fmt = FORMATS[op];
  if (op === "SET") return { uses: [], defs: [a[0]] };
  if (op === "INCREMENT" || op === "DECREMENT") return { uses: [a[0]], defs: [a[0]] };
  if (op === "SPREAD_INTO") return { uses: [a[0], a[1]], defs: [a[0]] };
  if (op === "FUNC_CALL") return { uses: [a[0], a[2], ...a[3]], defs: [a[1]] };
  if (op === "FUNC_ARRAY_CALL" || op === "FUNC_ARRAY_CALL_AWAIT") return { uses: [a[0], a[2], a[3]], defs: [a[1]] };
  if (op === "SET_PROP" || op === "SET_INDEX") return { uses: [a[0], a[1], a[2]], defs: [] };
  if (op === "JUMP_EQ" || op === "JUMP_NOT_EQ" || op === "THROW" || op === "THROW_ARGUMENT" || op === "PRINT") return { uses: [a[0]], defs: [] };
  if (op === "LOAD_ARRAY") return { uses: [...a[1]], defs: [a[0]] };
  if (op === "LOAD_OBJECT") return { uses: [...a[1], ...a[2]], defs: [a[0]] };
  if (op === "JUMP_UNCONDITIONAL" || op === "NOP" || op === "END") return { uses: [], defs: [] };
  if (op.startsWith("LOAD_") || op === "SETUP_OBJECT" || op === "SETUP_ARRAY" || op === "SET_NULL" || op === "SET_UNDEFINED") return { uses: [], defs: [a[0]] };
  // dest-first ops: dest, then source registers
  const regs = [...fmt].map((k, i) => (k === "r" ? a[i] : null));
  return { uses: regs.slice(1).filter((r) => r !== null), defs: [regs[0]] };
}

/**
 * @param ins      disassembly
 * @param codeLen  bytecode length (falling off the end = return)
 * @param opts     { deps: Map(reg -> {name, kind:'param'|'outer', direct:boolean}), outReg, isAsync }
 * @returns JS source of the function body
 */
export function liftFunction(ins, codeLen, opts) {
  for (const x of ins) {
    if (UNSUPPORTED.has(x.op)) throw new LiftError(`${x.op} not lifted yet`);
    const { uses, defs } = regIO(x);
    if (defs.some((r) => r === IP || r === UNDEF)) throw new LiftError("write to a reserved register");
    if (uses.includes(IP)) throw new LiftError("reads the instruction pointer");
    if (x.op === "FUNC_ARRAY_CALL_AWAIT" && !opts.isAsync) throw new LiftError("await outside an async wrapper");
  }
  const byAddr = new Map(ins.map((x, i) => [x.addr, i]));
  const endAddr = codeLen;

  /* ---------- basic blocks ---------- */
  const leaders = new Set([0]);
  ins.forEach((x, i) => {
    if (x.op === "JUMP_UNCONDITIONAL" || x.op === "JUMP_EQ" || x.op === "JUMP_NOT_EQ") {
      const tgt = x.args[x.op === "JUMP_UNCONDITIONAL" ? 0 : 1];
      if (tgt !== endAddr) leaders.add(tgt);
    }
    if (TERMINATORS.has(x.op) && i + 1 < ins.length) leaders.add(ins[i + 1].addr);
  });
  const starts = [...leaders].filter((a) => byAddr.has(a)).sort((a, b) => a - b);
  const blocks = starts.map((s, k) => {
    const from = byAddr.get(s), to = k + 1 < starts.length ? byAddr.get(starts[k + 1]) : ins.length;
    return { start: s, list: ins.slice(from, to), idx: k };
  });
  const blockAt = new Map(blocks.map((b) => [b.start, b]));
  const next = (b) => blocks[b.idx + 1] || null;
  const tgtOf = (x) => x.args[x.op === "JUMP_UNCONDITIONAL" ? 0 : 1];
  for (const b of blocks) {
    const last = b.list[b.list.length - 1];
    b.succ = [];
    if (last.op === "JUMP_UNCONDITIONAL") b.succ.push(tgtOf(last));
    else if (last.op === "JUMP_EQ" || last.op === "JUMP_NOT_EQ") b.succ.push(tgtOf(last), next(b) ? next(b).start : endAddr);
    else if (last.op === "THROW" || last.op === "THROW_ARGUMENT" || last.op === "END") { /* none (END = return) */ }
    else b.succ.push(next(b) ? next(b).start : endAddr);
  }

  /* ---------- block-local constant propagation ---------- */
  // fold[i][k] = literal for operand register k of instruction i (by register), when known
  const constIn = new Map(); // instruction -> Map(reg -> value) before it
  const constOut = new Map(); // instruction -> {v} when its result is a known primitive
  for (const b of blocks) {
    const known = new Map(b.start === 0 ? [[UNDEF, undefined], [VOIDR, 0]] : [[UNDEF, undefined]]);
    if (b.start === 0) for (const [r] of opts.deps) known.delete(r);
    for (const x of b.list) {
      constIn.set(x, new Map(known));
      const a = x.args;
      const val = (r) => (known.has(r) ? { v: known.get(r) } : null);
      let out = null;
      switch (x.op) {
        case "LOAD_BYTE": case "LOAD_DWORD": case "LOAD_FLOAT": case "LOAD_STRING": case "LOAD_BOOL": out = { v: a[1] }; break;
        case "SET": out = { v: a[1] }; break;
        case "SET_NULL": out = { v: null }; break;
        case "SET_UNDEFINED": out = { v: undefined }; break;
        case "SET_REF": out = val(a[1]); break;
        case "INCREMENT": { const p = val(a[0]); out = p && typeof p.v === "number" ? { v: p.v + 1 } : null; break; }
        case "DECREMENT": { const p = val(a[0]); out = p && typeof p.v === "number" ? { v: p.v - 1 } : null; break; }
        default:
          if (BINOPS[x.op]) {
            const l = val(a[1]), r = val(a[2]);
            // primitives only: no user code can run
            if (l && r && isPrim(l.v) && isPrim(r.v)) out = { v: Function("a", "b", `return a ${BINOPS[x.op]} b`)(l.v, r.v) };
          } else if (["TEST", "TEST_NEQ", "NOT", "NEGATE", "PLUS", "BNOT", "TYPEOF", "VOID"].includes(x.op)) {
            const p = val(a[1]);
            if (p && isPrim(p.v)) {
              const v = p.v;
              out = { v: x.op === "TEST" ? !!v : x.op === "TEST_NEQ" || x.op === "NOT" ? !v : x.op === "NEGATE" ? -v : x.op === "PLUS" ? +v : x.op === "BNOT" ? ~v : x.op === "TYPEOF" ? typeof v : undefined };
            }
          }
      }
      if (out) constOut.set(x, out);
      for (const d of regIO(x).defs) known.delete(d);
      if (out && regIO(x).defs.length === 1) known.set(regIO(x).defs[0], out.v);
    }
  }
  const folded = (x, r) => constIn.get(x).has(r);
  // a conditional jump on a known constant is really a jump (or nothing): rewrite and start over
  {
    let changed = false;
    const ins2 = ins.map((x) => {
      if ((x.op === "JUMP_EQ" || x.op === "JUMP_NOT_EQ") && constIn.get(x).has(x.args[0])) {
        changed = true;
        const v = constIn.get(x).get(x.args[0]);
        const taken = x.op === "JUMP_EQ" ? !!v : !v;
        return taken ? { ...x, op: "JUMP_UNCONDITIONAL", args: [x.args[1]] } : { ...x, op: "NOP", args: [] };
      }
      return x;
    });
    if (changed) return liftFunction(ins2, codeLen, opts);
  }
  // reachability
  const reach = new Set();
  for (const st = [0]; st.length;) { const a = st.pop(); if (a === endAddr || reach.has(a)) continue; reach.add(a); for (const s of blockAt.get(a).succ) st.push(s); }

  /* ---------- liveness (uses that were folded don't count) ---------- */
  const realUses = (x) => regIO(x).uses.filter((r) => !folded(x, r) && r !== UNDEF);
  for (const b of blocks) {
    b.use = new Set(); b.def = new Set();
    for (const x of b.list) {
      for (const r of realUses(x)) if (!b.def.has(r)) b.use.add(r);
      for (const d of regIO(x).defs) b.def.add(d);
    }
    b.liveIn = new Set(); b.liveOut = new Set();
  }
  const outLive = new Set([opts.outReg]); // read when execution ends
  for (let changed = true; changed;) {
    changed = false;
    for (let k = blocks.length - 1; k >= 0; k--) {
      const b = blocks[k];
      const out = new Set();
      const last = b.list[b.list.length - 1];
      if (b.succ.includes(endAddr) || last.op === "END") for (const r of outLive) out.add(r);
      for (const s of b.succ) if (s !== endAddr) for (const r of blockAt.get(s).liveIn) out.add(r);
      const inn = new Set(b.use);
      for (const r of out) if (!b.def.has(r)) inn.add(r);
      if (out.size !== b.liveOut.size || inn.size !== b.liveIn.size) changed = true;
      b.liveOut = out; b.liveIn = inn;
    }
  }

  /* ---------- names ---------- */
  const names = new Map();
  let vcount = 0;
  const writtenRegs = new Set(ins.flatMap((x) => regIO(x).defs));
  const prologue = [];
  for (const [r, d] of opts.deps) {
    if (d.kind === "param" || (d.direct && !writtenRegs.has(r))) names.set(r, d.name);
    else { const nm = `${d.name}$`; names.set(r, nm); prologue.push(`let ${nm} = ${d.name};`); }
  }
  const nameOf = (r) => {
    if (r === UNDEF) return "void 0";
    if (!names.has(r)) names.set(r, `v${++vcount}`);
    return names.get(r);
  };
  const entry = blocks[0];
  const localDecls = new Set();

  /* ---------- per-block emission with pending expressions ---------- */
  function emitBlock(b) {
    const out = [];
    const pend = new Map(); // reg -> {code, eff, seq, reads:Set<reg>}
    let seq = 0;
    const effList = () => [...pend.entries()].filter(([, p]) => p.eff).sort((x, y) => x[1].seq - y[1].seq);
    const assign = (r, code) => { localDecls.add(r); out.push(`${nameOf(r)} = ${code};`); };
    const flushOne = (r) => { const p = pend.get(r); pend.delete(r); assign(r, p.code); };
    const flushEff = () => { for (const [r] of effList()) flushOne(r); };
    const flushReaders = (reg) => {
      const readers = [...pend.entries()].filter(([, p]) => p.reads.has(reg));
      if (readers.some(([, p]) => p.eff)) flushEff();
      for (const [r] of readers) if (pend.has(r)) flushOne(r);
    };
    // how many uses r's value gets in this block (from instruction j on), and if it's live after
    const usage = (j, r) => {
      let n = 0;
      for (let k = j + 1; k < b.list.length; k++) {
        const y = b.list[k];
        n += realUses(y).filter((u) => u === r).length;
        if (regIO(y).defs.includes(r)) return { n, liveAfter: false };
      }
      return { n, liveAfter: b.liveOut.has(r) };
    };
    /* operand: returns {code, eff, seq, reads} and consumes a pending */
    let consumed = [];
    const take = (x, r) => {
      const c = constIn.get(x);
      if (c.has(r)) return { code: lit(c.get(r)), eff: false, reads: new Set() };
      if (r === UNDEF) return { code: "void 0", eff: false, reads: new Set() };
      if (pend.has(r)) { const p = pend.get(r); pend.delete(r); consumed.push(p); return p; }
      return { code: nameOf(r), eff: false, reads: new Set([r]) };
    };
    // ensure consumed effectful pendings evaluate in order and after nothing newer
    const checkOrder = (ops, effectfulConsumer) => {
      const effs = ops.filter((o) => o.eff && o.seq !== undefined);
      const seqs = effs.map((o) => o.seq);
      const inOrder = seqs.every((s, i) => i === 0 || s > seqs[i - 1]);
      const remaining = effList();
      const minC = seqs.length ? Math.min(...seqs) : Infinity;
      const newerLeft = remaining.some(([, p]) => p.seq > minC);
      // (older pendings stay pending: they are flushed first when something is emitted now)
      return !(!inOrder || newerLeft);
    };
    /** materialise operands as variables when ordering can't be kept */
    const fallback = (x, regs) => {
      // put back what we took, then flush everything in order
      for (const p of consumed) pend.set(p.reg, p);
      consumed = [];
      flushEff();
      for (const [r] of [...pend.entries()]) flushOne(r);
      return regs.map((r) => take(x, r));
    };
    const result = (j, x, r, expr) => {
      // expr: {code, eff, reads}
      if (constOut.has(x) && !expr.eff) expr = { code: lit(constOut.get(x).v), eff: false, reads: new Set() };
      else if (constOut.has(x)) {
        // a constant computed from constants: operands were primitives, nothing observable runs
        expr = { code: lit(constOut.get(x).v), eff: false, reads: new Set() };
      }
      flushReaders(r);
      const { n, liveAfter } = usage(j, r);
      if (n === 1 && !liveAfter) { pend.set(r, { ...expr, reg: r, seq: expr.eff ? expr.seq ?? ++seq : undefined }); return; }
      if (n === 0 && !liveAfter) { if (expr.eff) { flushEff(); out.push(`${expr.code};`); } return; }
      if (expr.eff) flushEff();
      assign(r, expr.code);
    };
    const unionReads = (ops) => new Set(ops.flatMap((o) => [...o.reads]));

    /* SETUP_ARRAY dest,n + SET_INDEX dest,k,v for k = 0..n-1 + one consuming use => an array literal */
    const builderOK = (j, dest, n) => {
      let k = 0;
      for (let q = j + 1; q < b.list.length; q++) {
        const y = b.list[q];
        const io = regIO(y);
        if (y.op === "SET_INDEX" && y.args[0] === dest && k < n) {
          const c = constIn.get(y);
          if (!c.has(y.args[1]) || c.get(y.args[1]) !== k || y.args[2] === dest) return false;
          k++; continue;
        }
        const usesDest = realUses(y).filter((u) => u === dest).length;
        if (!usesDest) { if (io.defs.includes(dest)) return false; continue; }
        if (k !== n || usesDest !== 1) return false;
        if (io.defs.includes(dest)) return true;
        const u = usage(q, dest);
        return u.n === 0 && !u.liveAfter;
      }
      return false;
    };
    const otherEffNewer = (bl) => effList().some(([r, p]) => r !== bl.reg && bl.seq !== undefined && p.seq > bl.seq);

    for (let j = 0; j < b.list.length; j++) {
      const x = b.list[j], a = x.args, op = x.op;
      consumed = [];
      // all operands known primitives: the result is a constant and nothing observable runs
      if (constOut.has(x) && regIO(x).defs.length === 1) {
        result(j, x, regIO(x).defs[0], { code: lit(constOut.get(x).v), eff: false, reads: new Set() });
        continue;
      }
      if (op === "SETUP_ARRAY" && a[1] >= 0 && builderOK(j, a[0], a[1])) {
        flushReaders(a[0]);
        pend.set(a[0], { builder: true, reg: a[0], slots: [], eff: false, seq: undefined, reads: new Set(), get code() { return `[${this.slots.join(", ")}]`; } });
        continue;
      }
      if (op === "SET_INDEX" && pend.get(a[0])?.builder) {
        const bl = pend.get(a[0]);
        if (otherEffNewer(bl)) flushOne(a[0]);
        else {
          pend.delete(a[0]);
          const [v] = (() => { let o = [take(x, a[2])]; if (!checkOrder(o, false)) o = fallback(x, [a[2]]); return o; })();
          bl.slots.push(v.code);
          if (v.eff) { bl.eff = true; if (bl.seq === undefined) bl.seq = v.seq ?? ++seq; }
          for (const r of v.reads) bl.reads.add(r);
          pend.set(a[0], bl);
          continue;
        }
      }
      const gather = (regs, effectful) => {
        let ops = regs.map((r) => take(x, r));
        if (!checkOrder(ops, effectful)) ops = fallback(x, regs);
        return ops;
      };
      const effSeq = (ops) => { const s = ops.filter((o) => o.eff).map((o) => o.seq); return s.length ? Math.min(...s) : undefined; };
      const pureExpr = (code, ops) => ({ code, eff: ops.some((o) => o.eff), seq: effSeq(ops), reads: unionReads(ops) });
      const effExpr = (code, ops) => ({ code, eff: true, seq: effSeq(ops) ?? ++seq, reads: unionReads(ops) });
      switch (op) {
        case "LOAD_BYTE": case "LOAD_DWORD": case "LOAD_FLOAT": case "LOAD_STRING": case "LOAD_BOOL": case "SET":
        case "SET_NULL": case "SET_UNDEFINED": {
          const v = op === "SET_NULL" ? null : op === "SET_UNDEFINED" ? undefined : a[1];
          result(j, x, a[0], { code: lit(v), eff: false, reads: new Set() }); break;
        }
        case "SET_REF": { const [s] = gather([a[1]], false); result(j, x, a[0], pureExpr(s.code, [s])); break; }
        case "LOAD_ARRAY": { const ops = gather(a[1], false); result(j, x, a[0], pureExpr(`[${ops.map((o) => o.code).join(", ")}]`, ops)); break; }
        case "LOAD_OBJECT": {
          const ops = gather([...a[1], ...a[2]], true);
          const ks = ops.slice(0, a[1].length), vs = ops.slice(a[1].length);
          const tmp = "o";
          const body = ks.map((k, i) => `${tmp}[${k.code}] = ${vs[i].code}`).join(", ");
          result(j, x, a[0], effExpr(`((${tmp}) => (${body}${body ? ", " : ""}${tmp}))({})`, ops)); break;
        }
        case "SETUP_OBJECT": result(j, x, a[0], { code: "{}", eff: false, reads: new Set() }); break;
        case "SETUP_ARRAY": result(j, x, a[0], { code: `new Array(${a[1]})`, eff: false, reads: new Set() }); break;
        case "INIT_CONSTRUCTOR": {
          const ops = gather([a[1], a[2]], true);
          result(j, x, a[0], effExpr(ops[1].builder ? `new (${ops[0].code})(${ops[1].slots.join(", ")})` : `new (${ops[0].code})(...${ops[1].code})`, ops)); break;
        }
        case "FUNC_CALL": {
          const ops = gather([a[0], a[2], ...a[3]], true);
          result(j, x, a[1], effExpr(`(${ops[0].code}).call(${ops.slice(1).map((o) => o.code).join(", ")})`, ops)); break;
        }
        case "FUNC_ARRAY_CALL": case "FUNC_ARRAY_CALL_AWAIT": {
          const ops = gather([a[0], a[2], a[3]], true);
          const aw = op === "FUNC_ARRAY_CALL_AWAIT" ? "await " : "";
          const [fn, th, args] = ops;
          let code;
          if (args.builder) {
            const list = args.slots.join(", ");
            if (fn.member && fn.member.simple && fn.member.obj === th.code) code = `${fn.member.obj}[${fn.member.prop}](${list})`;
            else if (th.code === "void 0") code = /^[A-Za-z_$][\w$]*$/.test(fn.code) ? `${fn.code}(${list})` : `(0, ${fn.code})(${list})`;
            else code = `(${fn.code}).call(${th.code}${list ? ", " + list : ""})`;
          } else code = `(${fn.code}).apply(${th.code}, ${args.code})`;
          result(j, x, a[1], effExpr(`${aw}${code}`, ops)); break;
        }
        case "GET_PROP": case "GET_INDEX": {
          const ops = gather([a[1], a[2]], true);
          const e = effExpr(`(${ops[0].code})[${ops[1].code}]`, ops);
          e.member = { obj: ops[0].code, prop: ops[1].code, simple: !ops[0].eff && /^[A-Za-z_$][\w$]*$/.test(ops[0].code) };
          result(j, x, a[0], e); break;
        }
        case "SET_PROP": case "SET_INDEX": {
          const ops = gather([a[0], a[1], a[2]], true);
          flushEff();
          out.push(`(${ops[0].code})[${ops[1].code}] = ${ops[2].code};`); break;
        }
        case "INCREMENT": case "DECREMENT": {
          const [s] = gather([a[0]], true);
          result(j, x, a[0], effExpr(`${s.code} ${op === "INCREMENT" ? "+" : "-"} 1`, [s])); break;
        }
        case "TEST": { const [s] = gather([a[1]], false); result(j, x, a[0], pureExpr(`!!(${s.code})`, [s])); break; }
        case "TEST_NEQ": { const [s] = gather([a[1]], false); result(j, x, a[0], pureExpr(`!(${s.code})`, [s])); break; }
        case "VOID": { const [s] = gather([a[1]], false); result(j, x, a[0], pureExpr(`void (${s.code})`, [s])); break; }
        case "DELETE": { const [s] = gather([a[1]], false); result(j, x, a[0], pureExpr(`(${s.code}, true)`, [s])); break; }
        case "SPREAD": { const [s] = gather([a[1]], true); result(j, x, a[0], effExpr(`[...(${s.code})][0]`, [s])); break; }
        case "SPREAD_INTO": {
          const ops = gather([a[0], a[1]], true);
          result(j, x, a[0], effExpr(`((d, s) => d instanceof Array ? [...d, ...s] : d instanceof Object ? { ...d, ...s } : (() => { throw new Error("Cannot spread into non-object or non-array"); })())(${ops[0].code}, ${ops[1].code})`, ops)); break;
        }
        case "GET_ITERATOR": { const [s] = gather([a[1]], true); result(j, x, a[0], effExpr(`(${s.code})[Symbol.iterator]()`, [s])); break; }
        case "ITERATOR_NEXT": { const [s] = gather([a[1]], true); result(j, x, a[0], effExpr(`(${s.code}).next()`, [s])); break; }
        case "ITERATOR_DONE": { const [s] = gather([a[1]], true); result(j, x, a[0], effExpr(`(${s.code}).done`, [s])); break; }
        case "ITERATOR_VALUE": { const [s] = gather([a[1]], true); result(j, x, a[0], effExpr(`(${s.code}).value`, [s])); break; }
        case "GET_PROPERTIES": {
          const [s] = gather([a[1]], true);
          result(j, x, a[0], effExpr(`((o) => { const k = Object.getOwnPropertyNames(o); if (o instanceof Array) k.pop(); return k; })(${s.code})`, [s])); break;
        }
        case "LOGICAL_AND": case "LOGICAL_OR": case "LOGICAL_NULLISH": {
          // both operands were already evaluated by the VM: the right one must not be deferred into a short-circuit
          const ops = gather([a[1], a[2]], false);
          let [l, rr] = ops;
          if (rr.eff) { const v = `t${++vcount}`; flushEff(); out.push(`const ${v} = ${rr.code};`); rr = { code: v, eff: false, reads: new Set() }; if (l.eff) throw new LiftError("ordering"); }
          const o = op === "LOGICAL_AND" ? "&&" : op === "LOGICAL_OR" ? "||" : "??";
          result(j, x, a[0], pureExpr(`(${l.code}) ${o} (${rr.code})`, [l, rr])); break;
        }
        case "POWER": { const ops = gather([a[1], a[2]], true); result(j, x, a[0], effExpr(`Math.pow(${ops[0].code}, ${ops[1].code})`, ops)); break; }
        case "PRINT": { const [s] = gather([a[0]], true); flushEff(); out.push(`console.log(${s.code});`); break; }
        case "THROW": { const [s] = gather([a[0]], true); flushEff(); out.push(`throw new Error(${s.code});`); break; }
        case "THROW_ARGUMENT": { const [s] = gather([a[0]], true); flushEff(); out.push(`throw ${s.code};`); break; }
        case "JUMP_EQ": case "JUMP_NOT_EQ": {
          const [s] = gather([a[0]], true);
          b.cond = op === "JUMP_EQ" ? s.code : `!(${s.code})`; // jump taken when cond is true
          break;
        }
        case "JUMP_UNCONDITIONAL": case "NOP": case "END": break;
        default:
          if (BINOPS[op]) {
            const ops = gather([a[1], a[2]], !PURE_BIN.has(BINOPS[op]));
            const code = `(${ops[0].code}) ${BINOPS[op]} (${ops[1].code})`;
            result(j, x, a[0], PURE_BIN.has(BINOPS[op]) ? pureExpr(code, ops) : effExpr(code, ops));
          } else if (UNOPS[op]) {
            const [s] = gather([a[1]], !PURE_UN.has(op));
            const code = `${UNOPS[op]}(${s.code})`;
            result(j, x, a[0], PURE_UN.has(op) ? pureExpr(code, [s]) : effExpr(code, [s]));
          } else throw new LiftError("no lifting rule for " + op);
      }
    }
    if (pend.size) { flushEff(); for (const [r] of [...pend.entries()]) flushOne(r); }
    return out;
  }
  if (process.env.JSVDBG) for (const b of blocks) console.error("blk", b.start, "succ", b.succ, "liveOut", [...b.liveOut].join(","));
  for (const b of blocks) b.code = reach.has(b.start) ? emitBlock(b) : [];

  /* ---------- structuring ---------- */
  const retStmt = () => `return ${names.has(opts.outReg) || writtenRegs.has(opts.outReg) ? nameOf(opts.outReg) : "null"};`;
  // loops: a back edge = unconditional jump to an earlier (or same) block
  const loops = new Map(); // head addr -> {latch addr (last back-edge block), exit addr}
  for (const b of blocks) {
    const last = b.list[b.list.length - 1];
    if (!reach.has(b.start)) continue;
    if (last.op === "JUMP_UNCONDITIONAL" && tgtOf(last) <= b.start) {
      const h = tgtOf(last);
      const exit = next(b) ? next(b).start : endAddr;
      const prev = loops.get(h);
      if (!prev || b.start > prev.latch) loops.set(h, { latch: b.start, exit });
    }
    if ((last.op === "JUMP_EQ" || last.op === "JUMP_NOT_EQ") && tgtOf(last) <= b.start) throw new LiftError("conditional back edge");
  }
  let steps = 0;
  function emitRange(from, until, loopStack) {
    const outL = [];
    let cur = from;
    while (cur !== until && cur !== endAddr) {
      if (++steps > 100000) throw new LiftError("structuring did not converge");
      const b = blockAt.get(cur);
      if (!b) throw new LiftError("jump into the middle of a block");
      const lp = loops.get(cur);
      if (lp && !(loopStack.length && loopStack[loopStack.length - 1].head === cur)) {
        const inner = emitRange(cur, -1, [...loopStack, { head: cur, latch: lp.latch, exit: lp.exit }]);
        outL.push(`for (;;) {`, ...inner.map((l) => "  " + l), `}`);
        cur = lp.exit;
        continue;
      }
      outL.push(...b.code);
      const last = b.list[b.list.length - 1];
      const L = loopStack[loopStack.length - 1];
      const jumpTo = (t) => {
        if (t === endAddr) return [retStmt()];
        if (L && t === L.head) return ["continue;"];
        if (L && t === L.exit) return ["break;"];
        if (loopStack.some((s) => s.head === t || s.exit === t)) throw new LiftError("labelled break/continue");
        return null;
      };
      if (last.op === "THROW" || last.op === "THROW_ARGUMENT") return outL;
      if (last.op === "END") { outL.push(retStmt()); return outL; }
      if (last.op === "JUMP_UNCONDITIONAL") {
        const t = tgtOf(last);
        if (L && b.start === L.latch && t === L.head) return outL; // the loop's own back edge
        const j = jumpTo(t);
        if (j) { outL.push(...j); return outL; }
        if (t === until) return outL;
        // a forward jump over code nothing reaches (a folded constant branch)
        if (t > b.start && blocks.every((o) => o.start <= b.start || o.start >= t || !reach.has(o.start))) { cur = t; continue; }
        throw new LiftError(`unstructured jump ${b.start} -> ${t}`);
      }
      if (last.op === "JUMP_EQ" || last.op === "JUMP_NOT_EQ") {
        const t = tgtOf(last), fall = next(b) ? next(b).start : endAddr;
        const j = jumpTo(t);
        if (j) { outL.push(`if (${b.cond}) {`, ...j.map((l) => "  " + l), `}`); cur = fall; continue; }
        if (t <= b.start) throw new LiftError("backward conditional jump");
        // if (!cond) { then: fall .. t } — with an else when the then-part ends in a forward jump past t
        const thenLast = ins[byAddr.get(t) - 1];
        let join = t, elseRange = null;
        if (thenLast && thenLast.op === "JUMP_UNCONDITIONAL" && tgtOf(thenLast) > t && !jumpTo(tgtOf(thenLast))
          && (until === -1 || tgtOf(thenLast) <= until || until === endAddr)) {
          join = tgtOf(thenLast); elseRange = [t, join];
        }
        // the then-part ends with the jump to the join (its block may also carry code)
        const thenCode = emitRange(fall, elseRange ? join : t, loopStack);
        const neg = b.cond.startsWith("!(") ? b.cond.slice(2, -1) : `!(${b.cond})`;
        outL.push(`if (${neg}) {`, ...thenCode.map((l) => "  " + l), `}`);
        if (elseRange) {
          const elseCode = emitRange(elseRange[0], elseRange[1], loopStack);
          outL[outL.length - 1] = `} else {`;
          outL.push(...elseCode.map((l) => "  " + l), `}`);
        }
        cur = join;
        continue;
      }
      // plain fall-through
      if (L && b.start === L.latch) return outL;
      cur = next(b) ? next(b).start : endAddr;
    }
    if (cur === endAddr && until !== endAddr) outL.push(retStmt());
    return outL;
  }
  const body = emitRange(0, endAddr, []);
  if (body[body.length - 1] !== retStmt()) body.push(retStmt());

  // declarations: registers live on entry start as the VM's initial values
  const decl = [];
  const entryInit = (r) => (r === VOIDR ? "0" : "null");
  for (const r of localDecls) {
    if ([...opts.deps.keys()].includes(r)) continue;
    decl.push(entry.liveIn.has(r) ? `${nameOf(r)} = ${entryInit(r)}` : nameOf(r));
  }
  for (const r of entry.liveIn) if (!opts.deps.has(r) && !localDecls.has(r) && r !== UNDEF) decl.push(`${nameOf(r)} = ${entryInit(r)}`);
  if (!localDecls.has(opts.outReg) && !opts.deps.has(opts.outReg) && names.has(opts.outReg) && !entry.liveIn.has(opts.outReg)) decl.push(`${nameOf(opts.outReg)} = null`);
  return [...prologue, decl.length ? `let ${[...new Set(decl)].join(", ")};` : "", ...body].filter(Boolean).join("\n");
}
