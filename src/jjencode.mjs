/**
 * Static decoder for JJEncode and AAEncode — utf-8.jp (Hasegawa Yosuke).
 *
 * Both encoders emit one expression of the shape
 *
 *   <prologue>  <seed>.$(<seed>.$(<seed>.$$+"\""+ DATA +"\")())();
 *
 * where DATA is a `+`-chain of string chunks and coercion expressions that
 * evaluates to the text  return "<escaped source>"  — and the final
 * Function(…)() call evaluates that text, resolving the `\<octal>` /
 * `\u<hex>` / `\"` / `\\` escapes to the original source.
 *
 * Decoding is therefore two pure string operations:
 *   1. walk the DATA token stream (string chunks + known coercion tokens) to
 *      rebuild the quoted body — no evaluation of any kind;
 *   2. resolve the JS string-literal escapes in that body.
 *
 * The canonical prologues below were extracted byte-exact from the real
 * encoders (test/fixtures/jjencode.cjs / aaencode.cjs); input whose prologue
 * deviates from them is a hard error rather than a guess.
 */

function fail(kind, msg) {
  throw new Error(`${kind}: ${msg}`);
}

function skipWs(s, i) {
  while (i < s.length && /\s/.test(s[i])) i++;
  return i;
}

/** Resolve JS (sloppy-mode) string-literal escapes in raw literal contents. */
function unescapeStringBody(kind, text) {
  let out = "";
  let i = 0;
  while (i < text.length) {
    const c = text[i];
    if (c !== "\\") {
      out += c;
      i++;
      continue;
    }
    const d = text[i + 1];
    if (d === undefined) fail(kind, "escape sequence ends at end of data");
    if (d === "u") {
      if (text[i + 2] === "{") fail(kind, "\\u{…} escape is not produced by the encoder — unknown shape");
      const hex = text.slice(i + 2, i + 6);
      if (!/^[0-9a-fA-F]{4}$/.test(hex)) fail(kind, `malformed \\u escape ${JSON.stringify(text.slice(i, i + 6))}`);
      out += String.fromCharCode(parseInt(hex, 16));
      i += 6;
      continue;
    }
    if (d === "x") {
      const hex = text.slice(i + 2, i + 4);
      if (!/^[0-9a-fA-F]{2}$/.test(hex)) fail(kind, `malformed \\x escape ${JSON.stringify(text.slice(i, i + 4))}`);
      out += String.fromCharCode(parseInt(hex, 16));
      i += 4;
      continue;
    }
    if (d >= "0" && d <= "7") {
      // LegacyOctalEscapeSequence (longest valid match): a first digit 0-3
      // may be followed by two more octal digits, 4-7 by one — so `\404`
      // is `\40` + literal `4`, and `\156` is one escape.
      const maxDigits = d >= "0" && d <= "3" ? 3 : 2;
      let j = i + 2, digits = d; // d = text[i+1] is already consumed
      while (j < text.length && digits.length < maxDigits && text[j] >= "0" && text[j] <= "7") digits += text[j++];
      out += String.fromCharCode(parseInt(digits, 8));
      i = j;
      continue;
    }
    if (d === "8" || d === "9") {
      out += d; // sloppy-mode \8 \9 are identity escapes
      i += 2;
      continue;
    }
    const simple = { n: "\n", r: "\r", t: "\t", b: "\b", f: "\f", v: "\v" };
    if (d in simple) {
      out += simple[d];
      i += 2;
      continue;
    }
    if (d === "\n") {
      i += 2; // line continuation
      continue;
    }
    out += d; // \" \\ \' and any other identity escape
    i += 2;
  }
  return out;
}

/**
 * Scan a JS string literal starting at i (quote at code[i]) and resolve its
 * escapes (level 1). The value contributes to the level-2 body text — e.g.
 * the chunk "\\\"" resolves to `\"`, which the final string literal in
 * `return "<body>"` then resolves to `"`.
 * Returns [value, next].
 */
function scanChunk(kind, code, i) {
  const quote = code[i];
  let raw = "";
  i++;
  while (i < code.length) {
    const c = code[i];
    if (c === "\\") {
      if (code[i + 1] === undefined) fail(kind, "string chunk ends in a backslash");
      raw += c + code[i + 1];
      i += 2;
      continue;
    }
    if (c === quote) return [unescapeStringBody(kind, raw), i + 1];
    raw += c;
    i++;
  }
  fail(kind, "string chunk is not closed");
}

// hex digit names for the jjencode seed object, in 0…f order
const JJ_DIGITS = ["___", "__$", "_$_", "_$$", "$__", "$_$", "$$_", "$$$", "$___", "$__$", "$_$_", "$_$$", "$$__", "$$_$", "$$$_", "$$$$"];

// canonical jjencode output for an empty input with the `$` prefix — the
// coercion prologue plus the `.$($.$($.$$+"\""+` data opener. Generated from
// the real encoder; output must start with exactly this (per gv substitution).
const JJ_PREFIX_DOLLAR = "$=~[];$={___:++$,$$$$:(![]+\"\")[$],__$:++$,$_$_:(![]+\"\")[$],_$_:++$,$_$$:({}+\"\")[$],$$_$:($[$]+\"\")[$],_$$:++$,$$$_:(!\"\"+\"\")[$],$__:++$,$_$:++$,$$__:({}+\"\")[$],$$_:++$,$$$:++$,$___:++$,$__$:++$};$.$_=($.$_=$+\"\")[$.$_$]+($._$=$.$_[$.__$])+($.$$=($.$+\"\")[$.__$])+((!$)+\"\")[$._$$]+($.__=$.$_[$.$$_])+($.$=(!\"\"+\"\")[$.__$])+($._=(!\"\"+\"\")[$._$_])+$.$_[$.$_$]+$.__+$._$+$.$;$.$$=$.$+(!\"\"+\"\")[$._$$]+$.__+$._+$.$+$.$$;$.$=($.___)[$.$_][$.$_];$.$($.$($.$$+\"\\\"\"+";

// …and the expression tail that closes the data segment
const JJ_TAIL = "+\"\\\"\")())();";

// canonical AAEncode prologue (empty input), up to and including the
// `(ﾟДﾟ)[ﾟoﾟ]+ ` data opener, with the expression tail separately
const AA_PREFIX = "ﾟωﾟﾉ= /｀ｍ´）ﾉ ~┻━┻   //*´∇｀*/ ['_']; o=(ﾟｰﾟ)  =_=3; c=(ﾟΘﾟ) =(ﾟｰﾟ)-(ﾟｰﾟ); (ﾟДﾟ) =(ﾟΘﾟ)= (o^_^o)/ (o^_^o);(ﾟДﾟ)={ﾟΘﾟ: '_' ,ﾟωﾟﾉ : ((ﾟωﾟﾉ==3) +'_') [ﾟΘﾟ] ,ﾟｰﾟﾉ :(ﾟωﾟﾉ+ '_')[o^_^o -(ﾟΘﾟ)] ,ﾟДﾟﾉ:((ﾟｰﾟ==3) +'_')[ﾟｰﾟ] }; (ﾟДﾟ) [ﾟΘﾟ] =((ﾟωﾟﾉ==3) +'_') [c^_^o];(ﾟДﾟ) ['c'] = ((ﾟДﾟ)+'_') [ (ﾟｰﾟ)+(ﾟｰﾟ)-(ﾟΘﾟ) ];(ﾟДﾟ) ['o'] = ((ﾟДﾟ)+'_') [ﾟΘﾟ];(ﾟoﾟ)=(ﾟДﾟ) ['c']+(ﾟДﾟ) ['o']+(ﾟωﾟﾉ +'_')[ﾟΘﾟ]+ ((ﾟωﾟﾉ==3) +'_') [ﾟｰﾟ] + ((ﾟДﾟ) +'_') [(ﾟｰﾟ)+(ﾟｰﾟ)]+ ((ﾟｰﾟ==3) +'_') [ﾟΘﾟ]+((ﾟｰﾟ==3) +'_') [(ﾟｰﾟ) - (ﾟΘﾟ)]+(ﾟДﾟ) ['c']+((ﾟДﾟ)+'_') [(ﾟｰﾟ)+(ﾟｰﾟ)]+ (ﾟДﾟ) ['o']+((ﾟｰﾟ==3) +'_') [ﾟΘﾟ];(ﾟДﾟ) ['_'] =(o^_^o) [ﾟoﾟ] [ﾟoﾟ];(ﾟεﾟ)=((ﾟｰﾟ==3) +'_') [ﾟΘﾟ]+ (ﾟДﾟ) .ﾟДﾟﾉ+((ﾟДﾟ)+'_') [(ﾟｰﾟ) + (ﾟｰﾟ)]+((ﾟｰﾟ==3) +'_') [o^_^o -ﾟΘﾟ]+((ﾟｰﾟ==3) +'_') [ﾟΘﾟ]+ (ﾟωﾟﾉ +'_') [ﾟΘﾟ]; (ﾟｰﾟ)+=(ﾟΘﾟ); (ﾟДﾟ)[ﾟεﾟ]='\\\\'; (ﾟДﾟ).ﾟΘﾟﾉ=(ﾟДﾟ+ ﾟｰﾟ)[o^_^o -(ﾟΘﾟ)];(oﾟｰﾟo)=(ﾟωﾟﾉ +'_')[c^_^o];(ﾟДﾟ) [ﾟoﾟ]='\\\"';(ﾟДﾟ) ['_'] ( (ﾟДﾟ) ['_'] (ﾟεﾟ+(ﾟДﾟ)[ﾟoﾟ]+ ";
const AA_TAIL = ") (ﾟΘﾟ)) ('_');";

// the ひだまりスケッチ easter egg inserts this before the main prologue
const AA_EGG = "X=_=3; \r\n\r\n    X / _ / X < \"来週も見てくださいね!\";\r\n\r\n";

/** Strip the demo page's "palindrome" wrapper, if present. */
function stripPalindrome(code) {
  // the demo page wraps:  LEAD + r + MID + rev(r) + TAIL, where r has its
  // trailing "," or ";" stripped first. Bytes dumped from the live page's own
  // keyup() expression:
  //   LEAD = 34,39,92,34,43,39,43,34,44   = "'\"+'+",
  //   MID  = 44,39,44                     = ",'",
  //   TAIL = 44,34,43,39,43,34,92,39,34   = ,"+'+\"'\"
  const LEAD = String.fromCharCode(34, 39, 92, 34, 43, 39, 43, 34, 44); // "'\"+'+",
  const END = String.fromCharCode(44, 34, 43, 39, 43, 34, 92, 39, 34); // ,"+'+\"'\"
  if (!code.startsWith(LEAD)) return code;
  const end = code.lastIndexOf(END);
  if (end < 0) fail("JJEncode", "palindrome wrapper has no matching tail");
  const middle = code.slice(LEAD.length, end);
  const sepAt = middle.lastIndexOf(",'"); // separator is ",'",  (comma-quote-comma)
  if (sepAt < 0) fail("JJEncode", "palindrome wrapper has no middle separator");
  const r = middle.slice(0, sepAt);
  const mirror = middle.slice(sepAt + 3); // skip ",'",  entirely
  if ([...mirror].reverse().join("") !== r) {
    fail("JJEncode", "palindrome mirror does not match the payload — unknown shape");
  }
  // the demo stripped the output's trailing ";" before wrapping — restore it
  return r + ";";
}

/**
 * Substitute the seed variable name into the canonical `$`-prefix. Object
 * KEYS (___, $$$$, __$, $$_$, …) and MEMBER names ($_, _$, $$, __, …) are
 * fixed names from the encoder's digit tables and must NOT be substituted —
 * only variable references are.
 */
function substituteGv(s, gv) {
  let out = "";
  let i = 0;
  while (i < s.length) {
    if (s[i] === "$") {
      const key = /^[\w$]+:/.exec(s.slice(i)); // object-literal key — verbatim
      if (!key) {
        out += gv;
        i++;
        if (s[i] === ".") {
          // <seed>.<member> — the member name is fixed, not gv-derived
          const member = /^[\w$]+/.exec(s.slice(i + 1));
          out += "." + member[0];
          i += 1 + member[0].length;
        }
        continue;
      }
      out += key[0];
      i += key[0].length;
      continue;
    }
    out += s[i];
    i++;
  }
  return out;
}

/**
 * Decode JJEncode output. `code` must be exactly one jjencode program.
 * Returns the original source text.
 */
export function decodeJjencode(code) {
  const kind = "JJEncode";
  code = code.trim();
  code = stripPalindrome(code);
  const m = /^([\w$]+)=~\[\];/.exec(code);
  if (!m) fail(kind, "missing the `<prefix>=~[];` seeding prologue");
  const gv = m[1];

  // the prologue is a fixed string per encoder — parameterised on the seed name
  const expected = substituteGv(JJ_PREFIX_DOLLAR, gv);
  if (!code.startsWith(expected)) {
    fail(kind, "prologue deviates from the canonical jjencode output — unknown variant");
  }
  if (!code.endsWith(JJ_TAIL)) fail(kind, "missing the data-segment tail");
  const start = expected.length;
  const end = code.length - JJ_TAIL.length;
  if (end < start) fail(kind, "data segment is empty in an unexpected way");

  // seg is the string-literal body of `return "<body>"` (the opening quote is
  // the last thing in the prefix, the closing quote the first in the tail)
  const seg = code.slice(start, end);
  const body = walkJjTokens(kind, gv, seg);
  return unescapeStringBody(kind, body);
}

/** Walk one jjencode DATA segment; returns the concatenated text. */
function walkJjTokens(kind, gv, seg) {
  let out = "";
  let i = 0;
  const skipPlus = () => {
    const j = skipWs(seg, i);
    if (seg[j] === "+") i = skipWs(seg, j + 1);
  };
  while (i < seg.length) {
    const c = seg[i];
    if (c === '"' || c === "'") {
      let chunk;
      [chunk, i] = scanChunk(kind, seg, i);
      out += chunk;
      skipPlus();
      continue;
    }
    // l-form:  (![]+"")[<gv>._$_]
    const lForm = `(![]+"")[${gv}._$_]`;
    if (seg.startsWith(lForm, i)) {
      out += "l";
      i += lForm.length;
      skipPlus();
      continue;
    }
    if (seg.startsWith(gv + ".", i)) {
      const rest = seg.slice(i + gv.length + 1);
      // longest-match: 4-char digit names before 3-char, then t / o / u
      let matched = null, val = null;
      for (const name of [...JJ_DIGITS.slice(8), ...JJ_DIGITS.slice(0, 8)]) {
        if (rest.startsWith(name)) { matched = name; val = JJ_DIGITS.indexOf(name).toString(16); break; }
      }
      if (!matched) {
        if (rest.startsWith("__")) { matched = "__"; val = "t"; }
        else if (rest.startsWith("_$")) { matched = "_$"; val = "o"; }
        else if (rest.startsWith("_")) { matched = "_"; val = "u"; }
      }
      if (!matched) fail(kind, `unknown seed property ${JSON.stringify(rest.slice(0, 8))}…`);
      out += val;
      i += gv.length + 1 + matched.length;
      skipPlus();
      continue;
    }
    fail(kind, `unexpected token at ${JSON.stringify(seg.slice(i, i + 16))}…`);
  }
  return out;
}

// AAEncode tokens, in encoder b-table order → hex digit 0…f. Tokens contain
// `+` internally, so the segment is consumed by longest-prefix match, never
// by splitting on `+`.
const AA_DIGITS = [
  "(c^_^o)",
  "(ﾟΘﾟ)",
  "((o^_^o) - (ﾟΘﾟ))",
  "(o^_^o)",
  "(ﾟｰﾟ)",
  "((ﾟｰﾟ) + (ﾟΘﾟ))",
  "((o^_^o) +(o^_^o))",
  "((ﾟｰﾟ) + (o^_^o))",
  "((ﾟｰﾟ) + (ﾟｰﾟ))",
  "((ﾟｰﾟ) + (ﾟｰﾟ) + (ﾟΘﾟ))",
  "(ﾟДﾟ) .ﾟωﾟﾉ",
  "(ﾟДﾟ) .ﾟΘﾟﾉ",
  "(ﾟДﾟ) ['c']",
  "(ﾟДﾟ) .ﾟｰﾟﾉ",
  "(ﾟДﾟ) .ﾟДﾟﾉ",
  "(ﾟДﾟ) [ﾟΘﾟ]",
];
const AA_SPECIALS = [
  ["(ﾟДﾟ)[ﾟoﾟ]", '"'],
  ["(ﾟДﾟ)[ﾟεﾟ]", "\\"],
  ["(oﾟｰﾟo)", "u"],
];
const AA_TOKENS = [
  ...AA_SPECIALS.map(([s, ch]) => ({ s: s.replace(/\s+/g, ""), ch })),
  ...AA_DIGITS.map((s, idx) => ({ s: s.replace(/\s+/g, ""), ch: idx.toString(16) })),
].sort((a, b) => b.s.length - a.s.length);

/** Whitespace-flexible prefix match of a (ws-normalised) token at seg[i]; returns next index or -1. */
function matchToken(seg, i, tok) {
  let j = i, k = 0;
  while (k < tok.length) {
    const tc = tok[k];
    if (/\s/.test(tc)) { k++; continue; } // token whitespace is optional in seg
    while (j < seg.length && /\s/.test(seg[j])) j++;
    if (j >= seg.length || seg[j] !== tc) return -1;
    j++;
    k++;
  }
  return j;
}

/** Decode AAEncode output. Returns the original source text. */
export function decodeAaencode(code) {
  const kind = "AAEncode";
  code = code.trim();
  // the ひだまりスケッチ easter egg adds its own statement before the prologue
  const eggAt = code.indexOf(AA_EGG);
  if (eggAt >= 0) code = (code.slice(0, eggAt) + code.slice(eggAt + AA_EGG.length)).trim();

  if (!code.startsWith(AA_PREFIX)) {
    fail(kind, "prologue deviates from the canonical aaencode output — unknown variant");
  }
  if (!code.endsWith(AA_TAIL)) fail(kind, "missing the kaomoji data tail");
  const seg = code.slice(AA_PREFIX.length, code.length - AA_TAIL.length);

  // consume tokens by longest-prefix match. The opening quote token is part
  // of the canonical prefix, so seg ends with the closing quote token;
  // everything before it is `\<octal>` / `\u<hex>` escape text.
  let data = "";
  let i = 0;
  while (i < seg.length) {
    i = skipWs(seg, i);
    if (seg[i] === "+") { i = skipWs(seg, i + 1); continue; }
    let matched = false;
    for (const tok of AA_TOKENS) {
      const next = matchToken(seg, i, tok.s);
      if (next >= 0) {
        data += tok.ch;
        i = next;
        matched = true;
        break;
      }
    }
    if (!matched) fail(kind, `unknown kaomoji token at ${JSON.stringify(seg.slice(i, i + 20))}…`);
  }
  // data = <body> + closing-quote token — the body itself contains only
  // escape sequences (every source char is emitted as \…), never a raw quote
  if (!data.endsWith('"')) fail(kind, "data segment does not end with a quote token");
  const body = data.slice(0, data.length - 1);
  if (body.endsWith('"') || body.startsWith('"')) {
    fail(kind, "unexpected raw quote inside the data body — unknown variant");
  }
  return unescapeStringBody(kind, body);
}
