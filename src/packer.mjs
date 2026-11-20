/**
 * Static unpacker for Dean Edwards' Packer — dean.edwards.name/packer.
 *
 * The packed form is
 *
 *   eval((function(p,a,c,k,e,d){…stub…})("payload",base,count,"kw|…".split("|"),0,{}))
 *
 * where the stub replaces word tokens e(0)…e(count-1) in the payload with the
 * matching keyword (or leaves them alone when the keyword is empty). The stub
 * IS the decoder, so the unpack is a pure string operation: no eval, no
 * execution. Two real-world stub families are recognised:
 *
 *   • the classic Dean Edwards stub (recursive base-62 encoder with
 *     `String.fromCharCode(c+29)`), seen on dean.edwards.name and thousands
 *     of malware samples;
 *   • the modern port used by DaftLogic ("Adapted joliclic's JavaScript
 *     packer"), whose encoders are `n.toString(base)`, a 0-9a-zA-Z digit
 *     table for base ≤ 62, and `String.fromCharCode(n%base+161)` for
 *     "High ASCII" (base 95).
 *
 * Both stubs have a fastDecode branch (`if(!''.replace(/^/,String))`) that
 * replaces every `\w+` (or `[\u00a1-\u00ff]+`) run through a dictionary —
 * that branch is the one modern engines take, and it is semantically
 * identical to the per-index branch. Anything else in a stub is unknown
 * shape → hard error, never guessed at.
 */

function fail(msg) {
  throw new Error(`Packer: ${msg}`);
}

/** Parse a JS string literal ('…' or "…") starting at i; returns [value, next]. */
function scanStringLiteral(s, i) {
  const quote = s[i];
  let out = "";
  i++;
  while (i < s.length) {
    const c = s[i];
    if (c === quote) return [out, i + 1];
    if (c === "\\") {
      const d = s[i + 1];
      if (d === undefined) fail("payload string ends in a backslash");
      // The payload is data; the packer only emits \" \\ \n style escapes via
      // JSON.stringify-style quoting. Resolve the standard ones, keep the
      // escape for anything else so the caller sees the real text.
      switch (d) {
        case "n": out += "\n"; i += 2; break;
        case "r": out += "\r"; i += 2; break;
        case "t": out += "\t"; i += 2; break;
        case "b": out += "\b"; i += 2; break;
        case "f": out += "\f"; i += 2; break;
        case "v": out += "\v"; i += 2; break;
        case "0": out += "\0"; i += 2; break;
        default: out += d; i += 2; break; // \" \\ \' \/ and identity escapes
      }
      continue;
    }
    out += c;
    i++;
  }
  fail("payload string literal is not closed");
}

/** Parse a decimal integer starting at i (no sign); returns [value, next]. */
function scanInt(s, i) {
  const start = i;
  while (i < s.length && s[i] >= "0" && s[i] <= "9") i++;
  if (i === start) fail(`expected an integer at offset ${i} of the unpacker arguments`);
  return [Number(s.slice(start, i)), i];
}

function skipWs(s, i) {
  while (i < s.length && /\s/.test(s[i])) i++;
  return i;
}

/**
 * Encode index c as a packer token for the given base/mode:
 *  - "toString": c.toString(base)                       (base ≤ 36)
 *  - "base62":   digits 0-9 a-z A-Z, most significant first
 *  - "latin1":   digits chr(base-digit + 161), least significant last
 */
function encodeToken(c, base, mode) {
  if (mode === "toString") return c.toString(base);
  let s = "";
  if (mode === "latin1") {
    do {
      s = String.fromCharCode((c % base) + 161) + s;
      c = Math.floor(c / base);
    } while (c > 0);
    return s;
  }
  // base62 — digit alphabet "0123456789abcdefghijklmnopqrstuvwxyz" +
  // "ABCDEFGHIJKLMNOPQRSTUVWXYZ" (same as the classic c>35 → chr(c+29) trick:
  // 36+29 = 'A' … 61+29 = 'Z')
  const digits = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
  do {
    s = digits[c % base] + s;
    c = Math.floor(c / base);
  } while (c > 0);
  return s;
}

/**
 * Unpack `code`. Returns the original source text. Throws (never guesses) when
 * the stub or arguments deviate from the known packer shapes.
 */
export function unpackPacker(code) {
  const open = code.indexOf("eval(");
  if (open !== 0) fail("input does not start with eval( — refusing to unpack mid-file");
  let i = skipWs(code, open + 5);
  // optional extra paren:  eval((function(…
  let extraParen = false;
  if (code[i] === "(") {
    // could also be a parenthesised function expression — treat as the
    // DaftLogic form only if `function` follows
    const j = skipWs(code, i + 1);
    if (code.startsWith("function", j) || code.startsWith("(function", j)) {
      extraParen = true;
      i = j;
    }
  }
  if (!code.startsWith("function", i)) fail("expected the unpacker function after eval(");
  // signature check
  const sigEnd = code.indexOf("{", i);
  const sig = code.slice(i, sigEnd);
  if (!/^function\s*\(\s*p\s*,\s*a\s*,\s*c\s*,\s*k\s*,\s*e\s*,\s*d\s*\)?$/.test(sig)) {
    fail(`unexpected unpacker parameter list ${JSON.stringify(sig)} — expected (p,a,c,k,e,d)`);
  }
  // scan the stub body (balanced braces)
  let depth = 0;
  const bodyStart = sigEnd;
  let bodyEnd = -1;
  for (let j = bodyStart; j < code.length; j++) {
    if (code[j] === "{") depth++;
    else if (code[j] === "}") { depth--; if (depth === 0) { bodyEnd = j + 1; break; } }
  }
  if (bodyEnd < 0) fail("unpacker stub braces are unbalanced");
  const stub = code.slice(bodyStart, bodyEnd);
  i = skipWs(code, bodyEnd);

  if (extraParen) {
    if (code[i] !== ")") fail("expected ) after the unpacker stub");
    i = skipWs(code, i + 1);
  }
  if (code[i] !== "(") fail("expected ( before the unpacker arguments");
  i = skipWs(code, i + 1);

  // ---- arguments: payload, base, count, keywords, …
  let payload;
  [payload, i] = scanStringLiteral(code, i);
  i = skipWs(code, i);
  if (code[i] !== ",") fail("expected , after the payload");
  i = skipWs(code, i + 1);

  let base;
  [base, i] = scanInt(code, i);
  i = skipWs(code, i);
  if (code[i] !== ",") fail("expected , after the base");
  i = skipWs(code, i + 1);

  let count;
  [count, i] = scanInt(code, i);
  i = skipWs(code, i);
  if (code[i] !== ",") fail("expected , after the word count");
  i = skipWs(code, i + 1);

  // keywords: "'a|b'.split('|')" | '"a|b".split("|")' | ['a','b']
  let keywords;
  if (code[i] === "'" || code[i] === '"') {
    let joined;
    [joined, i] = scanStringLiteral(code, i);
    const j = skipWs(code, i);
    const m = /^\.split\(\s*(['"])([\s\S])\1\s*\)/.exec(code.slice(j));
    if (!m) fail("expected .split(\"|\") after the keyword string");
    if (m[2] !== "|") fail(`keyword separator ${JSON.stringify(m[2])} is not the packer's "|"`);
    keywords = joined.split(m[2]);
    i = skipWs(code, j + m[0].length);
  } else if (code[i] === "[") {
    keywords = [];
    i = skipWs(code, i + 1);
    if (code[i] === "]") i++;
    else {
      while (true) {
        let kw;
        i = skipWs(code, i);
        if (code[i] !== "'" && code[i] !== '"') fail("keyword array must contain only string literals");
        [kw, i] = scanStringLiteral(code, i);
        keywords.push(kw);
        i = skipWs(code, i);
        if (code[i] === ",") { i++; continue; }
        if (code[i] === "]") { i++; break; }
        fail("malformed keyword array");
      }
    }
  } else {
    fail("expected the keyword list ('…'.split('|') or an array literal)");
  }

  // remaining args (0,{}) — tolerate but verify they are trivial
  const rest = code.slice(i);
  const closeIdx = rest.indexOf(")");
  if (closeIdx < 0) fail("unpacker arguments are not closed");
  const tail = rest.slice(0, closeIdx).trim();
  if (tail !== "" && !/^,\s*0\s*,\s*\{\s*\}$/.test(tail)) {
    fail(`unexpected trailing unpacker arguments ${JSON.stringify(tail)}`);
  }
  i = skipWs(code, i + closeIdx + 1);
  // the paren opened before `function` (if any) already closed right after the
  // stub — exactly ONE `)` remains here: eval's own closing paren
  if (code[i] !== ")") fail("expected closing ) for eval(");
  if (code.slice(i + 1).trim() !== "") fail("trailing code after the packed eval(…) expression");

  // ---- stub verification: known decoder markers only
  const flat = stub.replace(/\s+/g, "");
  if (!flat.includes("p=p.replace(newRegExp(") || !flat.includes("returnp")) {
    fail("stub does not contain the known token-replacement loop — unknown packer shape");
  }
  if (!/\.toString\(/.test(flat) && !/fromCharCode\(/.test(flat) && !/\.charAt\(/.test(flat)) {
    fail("stub contains no known token encoder (toString / fromCharCode / charAt)");
  }
  const fastDecode = flat.includes("if(!''.replace(/^/,String))") || flat.includes('if(!"".replace(/^/,String))');

  // token mode from the STUB's actual encoder (the port clamps base to
  // min(count, encoding), so a High-ASCII stub can carry a small base — the
  // mode cannot be inferred from the base alone):
  //   toString encoder:   e=function(n){return n.toString(<base>)}
  //   base62 digit table: s=a.charAt(n%<base>)   (classic Dean: fromCharCode(c+29))
  //   High ASCII:         String.fromCharCode(n%<base>+161)
  let mode;
  if (flat.includes("+161")) mode = "latin1";
  else if (/\.charAt\(/.test(flat) || /fromCharCode\(\s*\w+\s*\+\s*29\s*\)/.test(flat)) mode = "base62";
  else if (/\.toString\(/.test(flat)) mode = "toString";
  else fail("stub contains no known token encoder (toString / charAt / fromCharCode)");
  if (mode === "toString" && base > 36) {
    fail(`stub uses n.toString(base) but base ${base} exceeds 36 — unknown packer shape`);
  }
  if (mode === "base62" && base > 62) {
    fail(`stub uses a base-62 digit encoder but base is ${base} — unknown packer shape`);
  }
  // cross-check the base the stub's encoder embeds against the args base —
  // a mismatch means the stub and the arguments were doctored independently
  const embedded = mode === "toString"
    ? (/toString\((\d+)\)/.exec(flat) || [])[1]
    : mode === "latin1"
      ? (/fromCharCode\(\w+%(\d+)\+161\)/.exec(flat) || [])[1]
      : (/charAt\(\w+%(\d+)\)/.exec(flat) || [])[1];
  if (embedded !== undefined && Number(embedded) !== base) {
    fail(`stub encoder uses base ${embedded} but the arguments pass base ${base} — doctored input`);
  }
  if (mode === "base62" && /fromCharCode\(\s*\w+\s*\+\s*29\s*\)/.test(flat) && base !== 62) {
    fail("classic fromCharCode(c+29) encoder implies base 62 but the arguments disagree");
  }
  if (base < 2 || base > 95) fail(`base ${base} is outside the packer's 2…95 range`);
  if (count !== keywords.length) {
    fail(`word count ${count} does not match the ${keywords.length} supplied keywords`);
  }

  // ---- apply the replacements (pure string ops)
  const boundaryLatin1 = mode === "latin1";
  let p = payload;

  if (fastDecode) {
    // while(c--){d[e(c)]=k[c]||e(c)} … replace every \w+ (or latin-1 run)
    // through the dictionary. Every word in the payload is e(c) for some
    // c < count — a miss means we misread the shape, so error out.
    const dict = new Map();
    for (let c = 0; c < count; c++) dict.set(encodeToken(c, base, mode), keywords[c] || encodeToken(c, base, mode));
    const wordRe = boundaryLatin1 ? /[\u00a1-\u00ff]+/g : /\w+/g;
    p = p.replace(wordRe, (w) => {
      const repl = dict.get(w);
      if (repl === undefined) fail(`payload word ${JSON.stringify(w)} is not in the unpacker dictionary — unknown packer shape`);
      return repl;
    });
  } else {
    // per-index pass, descending c — exact order the stub uses. The original
    // passes k[c] as a replacement STRING, so $-patterns inside keywords are
    // interpreted by String.replace; reproduce that exactly.
    for (let c = count - 1; c >= 0; c--) {
      if (!keywords[c]) continue;
      const token = encodeToken(c, base, mode);
      if (boundaryLatin1) {
        p = p.split(token).join(keywords[c]);
      } else {
        p = p.replace(new RegExp("\\b" + token + "\\b", "g"), keywords[c]);
      }
    }
  }
  return p;
}
