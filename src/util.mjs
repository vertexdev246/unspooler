import * as t from "@babel/types";
import { ok } from "assert";

// ---------------------------------------------------------------- helpers
// Generic small helpers shared by passes.

export function makeUtil(tref) {
  return {
    simpleValueOf(node) {
      if (tref.isStringLiteral(node)) return { type: "string", value: node.value };
      if (tref.isNumericLiteral(node)) return { type: "number", value: node.value };
      if (tref.isBooleanLiteral(node)) return { type: "bool", value: node.value };
      if (tref.isNullLiteral(node)) return { type: "null", value: null };
      if (tref.isIdentifier(node, { name: "undefined" }))
        return { type: "undefined", value: undefined };
      if (
        tref.isUnaryExpression(node, { prefix: true, operator: "!" }) &&
        tref.isNumericLiteral(node.argument)
      )
        return { type: "bool", value: node.argument.value === 0 };
      if (
        tref.isUnaryExpression(node, { prefix: true, operator: "-" }) &&
        tref.isNumericLiteral(node.argument)
      )
        return { type: "number", value: -node.argument.value };
      return null;
    },
  };
}

/** Exact mirror of JS-Confuser's base91 decode (from src/transforms/string/encoding.ts). */
export function base91Decode(table, encoded) {
  const raw = "" + (encoded || "");
  const len = raw.length;
  const ret = [];
  let b = 0;
  let n = 0;
  let v = -1;
  for (let i = 0; i < len; i++) {
    const p = table.indexOf(raw[i]);
    if (p === -1) continue;
    if (v < 0) {
      v = p;
    } else {
      v += p * 91;
      b |= v << n;
      n += (v & 8191) > 88 ? 13 : 14;
      do {
        ret.push(b & 0xff);
        b >>= 8;
        n -= 8;
      } while (n > 7);
      v = -1;
    }
  }
  if (v > -1) {
    ret.push((b | (v << n)) & 0xff);
  }
  return bytesToString(ret);
}

/**
 * byte array -> string, byte-for-byte same semantics as their
 * utf8ArrayToStr / TextDecoder path.
 */
export function bytesToString(arr) {
  let result = "";
  const charCache = new Map();
  let i = 0;
  const buffLen = arr.length;
  while (i < buffLen) {
    const byte1 = arr[i++];
    let codePt;
    if (byte1 <= 0x7f) {
      codePt = byte1;
    } else if (byte1 <= 0xdf) {
      codePt = ((byte1 & 0x1f) << 6) | (arr[i++] & 0x3f);
    } else if (byte1 <= 0xef) {
      codePt = ((byte1 & 0x0f) << 12) | ((arr[i++] & 0x3f) << 6) | (arr[i++] & 0x3f);
    } else {
      codePt =
        ((byte1 & 0x07) << 18) |
        ((arr[i++] & 0x3f) << 12) |
        ((arr[i++] & 0x3f) << 6) |
        (arr[i++] & 0x3f);
    }
    const cached = charCache.get(codePt);
    if (cached !== undefined) {
      result += cached;
    } else {
      const s = String.fromCodePoint(codePt);
      charCache.set(codePt, s);
      result += s;
    }
  }
  return result;
}
