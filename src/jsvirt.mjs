/**
 * js-virtualizer (github.com/aesthetic0001/js-virtualizer) — bytecode
 * decoding and disassembly. Never executes the input: the bytecode blob is
 * base64 + zlib (pure data), and every instruction format below is read off
 * the VM's own operand readers (src/utils/opcodes.js, identical in
 * src/vm_dist.js).
 *
 * Opcode numbering: the default "RemoveUnused" pass shuffles opcode numbers
 * per build; the only copy of the mapping is the `opNames` string array in
 * the companion VM file. Without that file only the stock numbering (no
 * shuffle) can be used, and a disassembly that doesn't validate is refused.
 */
import zlib from "node:zlib";

export const STOCK_OPNAMES = ["LOAD_BYTE", "LOAD_BOOL", "LOAD_DWORD", "LOAD_FLOAT", "LOAD_STRING", "LOAD_ARRAY", "LOAD_OBJECT",
  "SETUP_OBJECT", "SETUP_ARRAY", "INIT_CONSTRUCTOR", "FUNC_CALL", "FUNC_ARRAY_CALL", "FUNC_ARRAY_CALL_AWAIT", "VFUNC_CALL",
  "VFUNC_SETUP_CALLBACK", "VFUNC_RETURN", "JUMP_UNCONDITIONAL", "JUMP_EQ", "JUMP_NOT_EQ", "TRY_CATCH_FINALLY", "THROW",
  "THROW_ARGUMENT", "SET", "SET_REF", "SET_PROP", "GET_PROP", "SET_INDEX", "GET_INDEX", "WRITE_EXT", "SET_NULL",
  "SET_UNDEFINED", "EQ_COERCE", "EQ", "NOT_EQ_COERCE", "NOT_EQ", "LESS_THAN", "LESS_THAN_EQ", "GREATER_THAN",
  "GREATER_THAN_EQ", "TEST", "TEST_NEQ", "ADD", "SUBTRACT", "MULTIPLY", "DIVIDE", "MODULO", "POWER", "AND", "BNOT", "OR",
  "XOR", "SHIFT_LEFT", "SHIFT_RIGHT", "SPREAD", "SPREAD_INTO", "NOT", "NEGATE", "PLUS", "INCREMENT", "DECREMENT", "TYPEOF",
  "VOID", "DELETE", "LOGICAL_AND", "LOGICAL_OR", "LOGICAL_NULLISH", "GET_ITERATOR", "ITERATOR_NEXT", "ITERATOR_DONE",
  "ITERATOR_VALUE", "GET_PROPERTIES", "NOP", "END", "PRINT"];

// operand kinds: r = register byte, b = raw byte, B = bool, d = dword (signed 32),
// f = float64, s = string, R = register list (len byte + bytes), o = jump offset (dword)
const BIN = "rrr", UN = "rr";
export const FORMATS = {
  LOAD_BYTE: "rb", LOAD_BOOL: "rB", LOAD_DWORD: "rd", LOAD_FLOAT: "rf", LOAD_STRING: "rs", LOAD_ARRAY: "rR",
  LOAD_OBJECT: "rRR", SETUP_OBJECT: "r", SETUP_ARRAY: "rd", INIT_CONSTRUCTOR: "rrr",
  FUNC_CALL: "rrrR", FUNC_ARRAY_CALL: "rrrr", FUNC_ARRAY_CALL_AWAIT: "rrrr",
  VFUNC_CALL: "orR", VFUNC_SETUP_CALLBACK: "orrBRR", VFUNC_RETURN: "rR",
  JUMP_UNCONDITIONAL: "o", JUMP_EQ: "ro", JUMP_NOT_EQ: "ro", TRY_CATCH_FINALLY: "roo", THROW: "r", THROW_ARGUMENT: "r",
  SET: "rb", SET_REF: "rr", SET_PROP: "rrr", GET_PROP: "rrr", SET_INDEX: "rrr", GET_INDEX: "rrr", WRITE_EXT: "rr",
  SET_NULL: "r", SET_UNDEFINED: "r",
  EQ_COERCE: BIN, EQ: BIN, NOT_EQ_COERCE: BIN, NOT_EQ: BIN, LESS_THAN: BIN, LESS_THAN_EQ: BIN, GREATER_THAN: BIN,
  GREATER_THAN_EQ: BIN, TEST: UN, TEST_NEQ: UN, ADD: BIN, SUBTRACT: BIN, MULTIPLY: BIN, DIVIDE: BIN, MODULO: BIN,
  POWER: BIN, AND: BIN, BNOT: UN, OR: BIN, XOR: BIN, SHIFT_LEFT: BIN, SHIFT_RIGHT: BIN, SPREAD: UN, SPREAD_INTO: UN,
  NOT: UN, NEGATE: UN, PLUS: UN, INCREMENT: "r", DECREMENT: "r", TYPEOF: UN, VOID: UN, DELETE: UN,
  LOGICAL_AND: BIN, LOGICAL_OR: BIN, LOGICAL_NULLISH: BIN, GET_ITERATOR: UN, ITERATOR_NEXT: UN, ITERATOR_DONE: UN,
  ITERATOR_VALUE: UN, GET_PROPERTIES: UN, NOP: "", END: "", PRINT: "r",
};

export class JsvError extends Error {}

/** base64 (+ zlib when the 0x78 0x9c header is present, exactly like the VM) */
export function decodeBlob(text, encoding = "base64") {
  const buf = Buffer.from(text, encoding);
  if (buf[0] === 0x78 && buf[1] === 0x9c) return zlib.inflateSync(buf);
  return buf;
}

/** the VM's readFloat: big-endian IEEE-754 double (its bit-twiddling is equivalent for finite values) */
function readFloat(code, at) {
  const dv = new DataView(new Uint8Array(code.subarray(at, at + 8)).buffer);
  return dv.getFloat64(0, false);
}

/**
 * Linear-sweep disassembly. Returns [{addr, op, args, size}] or throws JsvError.
 * Jump targets are absolute: the VM computes `cur + offset - 1` with cur = the
 * address right after the opcode byte, i.e. target = opcode address + offset.
 */
export function disassemble(code, opNames) {
  const out = [];
  let ip = 0;
  const need = (n) => { if (ip + n > code.length) throw new JsvError(`truncated instruction at ${ip}`); };
  const byte = () => (need(1), code[ip++]);
  const dword = () => { need(4); const v = (code[ip] << 24) | (code[ip + 1] << 16) | (code[ip + 2] << 8) | code[ip + 3]; ip += 4; return v; };
  while (ip < code.length) {
    const addr = ip;
    const opc = byte();
    const op = opNames[opc];
    if (op === undefined) throw new JsvError(`unknown opcode ${opc} at ${addr}`);
    const fmt = FORMATS[op];
    if (fmt === undefined) throw new JsvError(`no operand format for ${op}`);
    const args = [];
    for (const k of fmt) {
      if (k === "r" || k === "b") args.push(byte());
      else if (k === "B") args.push(byte() === 1);
      else if (k === "d") args.push(dword());
      else if (k === "o") args.push(addr + dword());
      else if (k === "f") { need(8); args.push(readFloat(code, ip)); ip += 8; }
      else if (k === "s") { const n = dword(); if (n < 0) throw new JsvError(`bad string length at ${addr}`); need(n); let s = ""; for (let i = 0; i < n; i++) s += String.fromCharCode(code[ip++]); args.push(s); }
      else if (k === "R") { const n = byte(); const regs = []; for (let i = 0; i < n; i++) regs.push(byte()); args.push(regs); }
    }
    out.push({ addr, op, args, size: ip - addr });
    if (op === "END" && ip === code.length) break;
  }
  // every jump / call target must land on an instruction boundary
  const starts = new Set(out.map((x) => x.addr));
  starts.add(code.length);
  for (const ins of out) {
    const fmt = FORMATS[ins.op];
    [...fmt].forEach((k, i) => {
      if (k === "o" && !starts.has(ins.args[i])) throw new JsvError(`${ins.op} at ${ins.addr} targets ${ins.args[i]}, not an instruction`);
    });
  }
  return out;
}

/**
 * Opcode table from a (deobfuscated) companion VM source: the array literal of
 * opcode-name strings: every one a stock name, non-NOP names unique.
 * RemoveUnused keeps only the used opcodes and pads with "NOP" — its padding
 * loop re-reads the growing array's length, so the table is usually shorter
 * than the stock 74 entries (e.g. 15 used ops -> 45 entries).
 */
export function opNamesFromVmSource(src) {
  const stock = new Set(STOCK_OPNAMES);
  const re = /\[\s*((?:"[A-Z_]+"|'[A-Z_]+')(?:\s*,\s*(?:"[A-Z_]+"|'[A-Z_]+'))+)\s*\]/g;
  let m;
  while ((m = re.exec(src))) {
    const names = m[1].split(",").map((x) => x.trim().slice(1, -1));
    if (names.length > STOCK_OPNAMES.length) continue;
    if (!names.every((n) => stock.has(n))) continue;
    // a real table: stock order, or a shuffle where every non-NOP name is unique
    const real = names.filter((n) => n !== "NOP");
    if (new Set(real).size !== real.length || real.length < 3) continue;
    return names;
  }
  return null;
}

/** pretty listing for comments / reports */
export function listing(ins) {
  return ins.map((x) => {
    const fmt = FORMATS[x.op];
    const a = x.args.map((v, i) => {
      const k = fmt[i];
      if (k === "r") return `r${v}`;
      if (k === "o") return `@${v}`;
      if (k === "R") return `[${v.map((r) => "r" + r).join(" ")}]`;
      if (k === "s") return JSON.stringify(v);
      return String(v);
    });
    return `${String(x.addr).padStart(5)}  ${x.op}${a.length ? " " + a.join(", ") : ""}`;
  }).join("\n");
}
