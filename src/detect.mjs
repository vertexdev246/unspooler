/**
 * Obfuscator fingerprinting from source text (cheap, no parse).
 *
 * Returns candidates sorted by score. Each carries the concrete signals that
 * fired, so the UI can show *why* — no guessing presented as fact.
 * JS-Confuser, javascript-obfuscator and JSFuck are reversible; the others
 * are recognised so the user is told plainly that support is on the roadmap.
 */

const count = (s, re) => (s.match(re) || []).length;
// obfuscator.io's base64 alphabet starts lowercase (raw or \x-escaped)
const isRc4 = (c) => /%\s*(?:0x100|256)\b/.test(c) || /\^\s*[\w$]+\[\s*\(\s*[\w$]+\[/.test(c);
const B64_LOWER = /abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789\+\/=|\\x61\\x62\\x63\\x64\\x65\\x66\\x67/;

const DETECTORS = [
  {
    id: "js-confuser",
    name: "JS-Confuser",
    url: "https://github.com/MichaelXF/js-confuser",
    supported: true,
    // Each transform: [name, level, test]. Packed code keeps its body inside
    // a string literal, so quotes may appear escaped (\") — regexes allow it.
    transforms: [
      ["Pack", "medium", (c) => /^\s*Function\(\s*\\?"[\w$]+\\?"\s*,\s*"/.test(c)],
      ["Control Flow Flattening", "medium", (c) =>
        /\b(?:0x9e3779b9|2654435769)\b/.test(c) || /while\s*\(\s*[\w$]+\(\s*[\w$]+\s*\)\s*!==\s*-?\d+\s*\)\s*switch/.test(c)],
      ["Global Concealing", "medium", (c) =>
        count(c, /case\s*\\?"[^"\\]{1,16}\\?"\s*:\s*return\s+[\w$]+\[\s*\\?"[\w$]+\\?"\s*\]/g) >= 5],
      ["Variable Masking", "medium", (c) => /\(\s*\.\.\.([\w$]+)\s*\)\s*\{\s*\1\[\s*\\?"length\\?"\s*\]\s*=/.test(c)],
      ["Flatten", "high", (c) => /function\s+[\w$]+\s*\(\s*[\w$]+\s*,\s*\[/.test(c)],
      ["String Encoding", "high", (c) => count(c, /\\{1,2}(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4})/g) >= 40],
      ["String Concealing", "low", (c) =>
        (/\*\s*(?:91|0x5b)\b/.test(c) && /\b(?:8191|0x1fff)\b/.test(c)) ||
        (/\.decode\(/.test(c) && /\.from\(/.test(c) && /utf-8/.test(c))],
      ["AST Scrambler", "low", (c) => /function\s+([\w$]+)\s*\(\)\s*\{\s*\1\s*=\s*function\s*\(\)\s*\{\s*\}\s*;?\s*\}/.test(c)],
      ["Dead Code", "low", (c) => /\\?"[\w$]{1,12}\\?"\s+in\s+[\w$]+\s*\)\s*\{/.test(c)],
      ["Dispatcher", "low", (c) => /\.apply\(this\)/.test(c) && /Object(?:\.create|\[\\?"create\\?"\])\(null\)/.test(c)],
      ["Duplicate Literals", "low", (c) => /\b(?:const|var)\s+[\w$]+\s*=\s*\[\s*0x0\s*,\s*0x1\s*,/.test(c)],
    ],
    test(code) {
      const signals = [];
      if (/"return this"|\\"return this\\"/.test(code) && /globalThis/.test(code) && /window/.test(code))
        signals.push("getGlobal helper (globalThis / window / \"return this\")");
      const found = this.transforms.filter(([, , t]) => t(code));
      for (const [name] of found) signals.push(`${name} fingerprint`);
      return signals;
    },
    details(code) {
      const found = this.transforms.filter(([, , t]) => t(code));
      const has = (lvl) => found.some(([, l]) => l === lvl);
      return {
        transforms: found.map(([n]) => n),
        // String Splitting / Calculator / Moved Declarations leave no reliable
        // text fingerprint, so this is a level estimate, not the exact options.
        preset: found.length === 0 ? null : has("high") ? "High" : has("medium") ? "Medium" : "Low",
      };
    },
  },
  {
    id: "javascript-obfuscator",
    name: "javascript-obfuscator (obfuscator.io)",
    url: "https://github.com/javascript-obfuscator/javascript-obfuscator",
    supported: true,
    // Presets build on each other (default < low < medium < high), so the
    // strongest feature present gives the level estimate.
    transforms: [
      ["Debug Protection", "high", (c) => /debu['"]\s*\+\s*['"]gger|\\x64\\x65\\x62\\x75['"]\s*\+/.test(c) || (/['"]stateObject['"]/.test(c) && /['"]counter['"]/.test(c))],
      ["String Array (RC4)", "high", (c) => B64_LOWER.test(c) && isRc4(c)],
      ["String Array (base64)", "medium", (c) => B64_LOWER.test(c) && !isRc4(c)],
      ["Control Flow Flattening", "medium", (c) => /switch\s*\(\s*[\w$]+\[\s*[\w$]+\+\+\s*\]\s*\)/.test(c)],
      ["Control-flow storage objects", "medium", (c) =>
        count(c, /(?:['"]?[A-Za-z]{5}['"]?\s*:|\[\s*['"][A-Za-z]{5}['"]\s*\]\s*=)\s*function\s*\(\s*[\w$]+\s*,\s*[\w$]+\s*\)\s*\{\s*return\s+[\w$]+\s*(?:===|!==|==|!=|<=|>=|[+\-*\/%<>&|^])\s*[\w$]+;?\s*\}/g) >= 2],
      ["Numbers to Expressions", "medium", (c) => count(c, /-?(?:0x[0-9a-f]+|\d+)\s*\*\s*-?(?:0x[0-9a-f]+|\d+)\s*\+\s*-?(?:0x[0-9a-f]+|\d+)\s*(?:\+|\*)/g) >= 3],
      ["Self Defending", "low", (c) => /\(\(\(\.\+\)\+\)\+\)\+\$|\\x28\\x28\\x28\\x2e\\x2b\\x29\\x2b\\x29\\x2b\\x29\\x2b\\x24/.test(c)],
      ["Disable Console Output", "low", (c) => /['"]exception['"]/.test(c) && /['"]table['"]/.test(c) && /['"]trace['"]/.test(c)],
      ["String Array", "default", (c) => /([\w$]+)\s*=\s*function\s*\(\)\s*\{\s*return\s+[\w$]+;?\s*\}\s*;?\s*return\s+\1\(\)/.test(c)],
      ["String Array rotation", "default", (c) => /\[\s*['"]push['"]\s*\]\(\s*[\w$]+\[\s*['"]shift['"]\s*\]\(\)\s*\)|\.push\(\s*[\w$]+\.shift\(\)\s*\)/.test(c) && /parseInt\(/.test(c)],
    ],
    test(code) {
      const signals = [];
      const hexIds = count(code, /\b_0x[0-9a-f]{4,6}\b/g);
      if (hexIds >= 5) signals.push(`${hexIds} \`_0x…\` identifiers`);
      for (const [name] of this.transforms.filter(([, , t]) => t(code))) signals.push(`${name} fingerprint`);
      return signals;
    },
    details(code) {
      const found = this.transforms.filter(([, , t]) => t(code));
      const has = (lvl) => found.some(([, l]) => l === lvl);
      return {
        transforms: found.map(([n]) => n),
        preset: found.length === 0 ? null : has("high") ? "High" : has("medium") ? "Medium" : has("low") ? "Low" : "Default",
      };
    },
  },
  {
    id: "jsfuck",
    name: "JSFuck",
    url: "https://github.com/aemkei/jsfuck",
    supported: true,
    // The single []()!+ signal IS definitive — nothing else produces files
    // made of only those six characters — so skip the signal-count scaling.
    confidence: "high",
    test(code) {
      const body = code.replace(/\s+/g, "");
      if (body.length < 40) return [];
      const fuck = count(body, /[[\]()!+]/g);
      return fuck / body.length > 0.97 ? ["code made only of the six characters [ ] ( ) ! +"] : [];
    },
  },
  {
    id: "jsobfuscator-com",
    name: "js-obfuscator (javascriptobfuscator.com)",
    url: "https://github.com/caiguanhao/js-obfuscator",
    supported: true,
    test(code) {
      const signals = [];
      // legacy (npm 0.1.4 README form): a `_$_xxxx` or `_0x####` lookup table
      // of \x-escaped strings, indexed with `[0x0]`
      if (/var\s+_\$_[0-9a-f]{4}\s*=\s*\[/.test(code)) signals.push("`_$_xxxx` string table");
      if (/var\s+_0x[0-9a-f]{4}\s*=\s*\[\s*"/.test(code)) signals.push("`_0x####` \\x-escaped string table");
      // modern (live site 2026): a name-restore helper that resets
      // Function.prototype.name via getOwnPropertyDescriptor/defineProperty
      if (/getOwnPropertyDescriptor/.test(code) && /defineProperty/.test(code) &&
        /["']name["']/.test(code) && /configurable\s*:\s*(true|!0)/.test(code))
        signals.push("Function-name restore helper (getOwnPropertyDescriptor + defineProperty + `configurable: true`)");
      const hexEsc = count(code, /\\x[0-9A-Fa-f]{2}/g);
      if (hexEsc > 20) signals.push(`${hexEsc} \\x-escaped characters`);
      // modern shape without the helper (Replace Names only hit plain vars,
      // or Encode Strings with nothing to rename): program-level `var x,y;`
      // with null initializers, immediately followed by one IIFE that assigns
      // each of them (the encoder hoists top-level bindings out of it)
      if (/(?:^|;)\s*var\s+[A-Za-z_$][\w$]*(?:\s*,\s*[A-Za-z_$][\w$]*)*\s*;\s*\(function\s*\(\)\s*\{/.test(code)) {
        const vars = code.match(/(?:^|;)\s*var\s+([A-Za-z_$][\w$]*(?:\s*,\s*[A-Za-z_$][\w$]*)*)\s*;\s*\(function\s*\(\)\s*\{/);
        if (vars) {
          const names = vars[1].split(",").map((s) => s.trim());
          const iife = code.slice(vars.index);
          const end = iife.indexOf("})()") >= 0 ? iife.indexOf("})()") : iife.length;
          if (names.every((n) => new RegExp(`\\b${n.replace(/\$/g, "\\$")}\\s*=`).test(iife.slice(0, end))))
            signals.push(`hoisted top-level var${names.length > 1 ? "s" : ""} (${names.join(", ")}) assigned inside a single IIFE`);
        }
      }
      return signals;
    },
  },
  {
    // dean.edwards.name/packer — `eval(function(p,a,c,k,e,d){…}` base-62 unpacker
    id: "packer",
    name: "Dean Edwards' Packer",
    url: "https://dean.edwards.name/packer/",
    supported: true,
    // the `eval(function(p,a,c,k,e,d)` stub is definitive
    confidence: "high",
    test(code) {
      // classic single-paren `eval(function(p,a,c,k,e,d){…})` and the common
      // double-paren `eval((function(p,a,c,k,e,d){…})(…))` form alike
      return /\beval\s*\(\s*\(?\s*function\s*\(\s*p\s*,\s*a\s*,\s*c\s*,\s*k\s*,\s*e\s*,?\s*[d]?\s*\)/.test(code)
        ? ["`eval(function(p,a,c,k,e,d)` unpacker stub"] : [];
    },
  },
  {
    // utf-8.jp/public/jjencode.html — whole program into one seeded variable
    // (`$=~[];$=` with the default prefix; the prefix is configurable, so
    // match `<prefix>=~[];<prefix>=` generically)
    id: "jjencode",
    name: "JJEncode",
    url: "https://utf-8.jp/public/jjencode.html",
    supported: true,
    // the `<prefix>=~[];` seeding prologue is definitive
    confidence: "high",
    test(code) {
      return /(?:^|[;\s{])([\w$]+)=~\[\];\1=/.test(code) ? ["`<prefix>=~[];<prefix>=` variable-seeding prologue"] : [];
    },
  },
  {
    // utf-8.jp/public/aaencode.html — the same scheme written in kaomoji
    id: "aaencode",
    name: "AAEncode",
    url: "https://utf-8.jp/public/aaencode.html",
    supported: true,
    // the kaomoji prologue is definitive
    confidence: "high",
    test(code) {
      return /ﾟωﾟﾉ|｀ｍ´/.test(code) ? ["kaomoji (`ﾟωﾟﾉ`) variable prologue"] : [];
    },
  },
  {
    // anseki/gnirts — string-obfuscation only, between /* @mangle */ directives
    id: "gnirts",
    name: "gnirts",
    url: "https://github.com/anseki/gnirts",
    supported: true,
    test(code) {
      const signals = [];
      if (/Array\.prototype\.slice\.call\(arguments\),/.test(code) && /String\.fromCharCode\(/.test(code))
        signals.push("charcode-IIFE template (`Array.prototype.slice.call(arguments)` + `String.fromCharCode`)");
      if (/new RegExp\('\^\[\]\^\{/.test(code))
        signals.push("`new RegExp('^[^]{i}'+…)` match-piece template");
      if (/\(\d+\)\.toString\(36\)\.toLowerCase\(\)/.test(code))
        signals.push("base-36 piece template (`(n).toString(36).toLowerCase()`)");
      return signals;
    },
  },
  {
    id: "js-virtualizer",
    name: "js-virtualizer (VM)",
    url: "https://github.com/aesthetic0001/js-virtualizer",
    supported: true,
    test(code) {
      const signals = [];
      const loads = count(code, /\.loadFromString\(\s*['"][A-Za-z0-9+/=]{16,}['"]\s*,\s*['"]base64['"]\s*\)/g);
      if (loads) signals.push(`${loads} base64 bytecode blob(s) loaded into a VM`);
      if (/\.loadDependencies\(\s*\{/.test(code) && /\.registers\[\s*\d+\s*\]/.test(code)) signals.push("VM register file read back as the return value");
      if (/new\s+JSVM\s*\(/.test(code)) signals.push("`new JSVM()`");
      // the companion VM file itself
      if (/\b(?:LOAD_DWORD|FUNC_ARRAY_CALL|VFUNC_SETUP_CALLBACK)\b/.test(code) && /readDWORD|loadFromString/.test(code)) signals.push("js-virtualizer VM implementation (opcode table)");
      return signals;
    },
  },
  {
    id: "evalpack",
    name: "Eval packer",
    url: "https://github.com/lelinhtinh/de4js",
    supported: true,
    test(code) {
      const signals = [];
      if (/\beval\s*\(\s*(?:atob|unescape|decodeURIComponent|decodeURI)\s*\(/.test(code)) signals.push("eval() of a decode call (atob / unescape / decodeURIComponent)");
      if (/\b(?:new\s+)?Function\s*\(\s*(?:atob|unescape|decodeURIComponent)\s*\(/.test(code)) signals.push("Function() built from a decoded string");
      if (/\beval\s*\(\s*String\s*\.\s*fromCharCode\s*\(/.test(code)) signals.push("eval(String.fromCharCode(…))");
      return signals;
    },
  },
  {
    id: "jsdefender",
    name: "PreEmptive JSDefender",
    url: "https://www.preemptive.com/products/jsdefender/",
    supported: true,
    test(code) {
      const signals = [];
      if (/eval\("\(function [A-Za-z_$][\w$]*\([A-Za-z_$][\w$]*\)\{const [A-Za-z_$][\w$]*=[\w$.]+\([A-Za-z_$][\w$]*,[\w$.]+\([A-Za-z_$][\w$]*\.toString\(\)\)\);/.test(code))
        signals.push("self-defending eval loader keyed by a hash of its own source");
      if (/JSDEFENDER code has been tampered/.test(code)) signals.push("JSDefender tamper message");
      if (/Array\.prototype\.slice\.call\(arguments\);return eval\(/.test(code)) signals.push("arguments forwarded into an eval'd layer");
      return signals;
    },
  },
  {
    id: "jfogs",
    name: "jfogs",
    url: "https://github.com/zswang/jfogs",
    supported: true,
    // the $fog$<n> parameter scheme is the encoder's documented signature
    confidence: "high",
    test(code) {
      const n = count(code, /\$fog\$\d+/g);
      return n >= 3 ? [`${n} \`$fog$<n>\` hoisted-parameter identifiers`] : [];
    },
  },
  {
    // sojson.com / jsjiami.com — jjencode-style seed + per-edition string
    // encryption. The encoder stamps a literal `jsjiami.com.vN` / `sojson.vN`
    // version string (usually at both the top and bottom of the file), so the
    // edition is read straight off that marker — never guessed.
    id: "sojson",
    name: "Sojson / jsjiami",
    url: "https://www.jsjiami.com/",
    supported: false,
    test(code) {
      const signals = [];
      const jj = code.match(/jsjiami\.com\.v(\d+)/i);
      if (jj) signals.push(`\`jsjiami.com.v${jj[1]}\` version marker`);
      const so = code.match(/\bsojson\.v(\d+)/i);
      if (so) signals.push(`\`sojson.v${so[1]}\` version marker`);
      if (!so && /\bsojson\s*=|\[["']sojson["']\]/.test(code)) signals.push("`sojson` seed variable");
      if (/\b(?:encode_version|version_)\s*=\s*['"]/.test(code)) signals.push("`version_` / `encode_version` seed variable");
      return signals;
    },
    details(code) {
      const m = code.match(/(?:jsjiami\.com\.v|sojson\.v)(\d+)/i);
      return { edition: m ? `V${m[1]}` : null };
    },
  },
  {
    // Commercial products: no stable public fingerprint; detect their brand
    // markers only (unverified against fresh builds — see HANDOFF §7.2b).
    id: "jscrambler",
    name: "JScrambler (commercial)",
    url: "https://jscrambler.com",
    supported: false,
    test(code) {
      return /jscrambler/i.test(code) ? ["`jscrambler` brand marker"] : [];
    },
  },
  {
    id: "jshaman",
    name: "JShaman (commercial)",
    url: "https://www.jshaman.com/",
    supported: false,
    test(code) {
      return /jshaman/i.test(code) ? ["`jshaman` brand marker"] : [];
    },
  },
  {
    // javascriptobfuscator.com (RichScripts) — a different product from the
    // caiguanhao `js-obfuscator` wrapper above. Per-build/commercial options
    // (code transposition, VM Proof Pack, self-compression); no stable public
    // output shape, so match only an explicit brand string.
    id: "richscripts",
    name: "JavaScript Obfuscator (javascriptobfuscator.com / RichScripts)",
    url: "https://javascriptobfuscator.com/",
    supported: false,
    test(code) {
      return /javascriptobfuscator\.com|RichScripts/i.test(code) ? ["`javascriptobfuscator.com` brand marker"] : [];
    },
  },
  {
    // ByteHide Shield — commercial. No published output signature; brand marker only.
    id: "bytehide",
    name: "ByteHide Shield (commercial)",
    url: "https://www.bytehide.com/",
    supported: false,
    test(code) {
      return /byte\s*hide/i.test(code) ? ["`ByteHide` brand marker"] : [];
    },
  },
  {
    // AfterPack — commercial. Brand marker only.
    id: "afterpack",
    name: "AfterPack (commercial)",
    url: "https://afterpack.dev/",
    supported: false,
    test(code) {
      return /afterpack/i.test(code) ? ["`afterpack` brand marker"] : [];
    },
  },
];

export function detectObfuscator(code) {
  const sample = code.length > 2_000_000 ? code.slice(0, 2_000_000) : code;
  const candidates = [];
  for (const d of DETECTORS) {
    const signals = d.test(sample);
    if (signals.length)
      candidates.push({
        id: d.id,
        name: d.name,
        url: d.url,
        supported: d.supported,
        signals,
        // A detector can override when its test is definitive on its own
        // (JSFuck: one signal, but nothing else produces []()!+-only files).
        // Otherwise confidence scales with the number of independent signals.
        confidence: d.confidence ?? (signals.length >= 3 ? "high" : signals.length === 2 ? "medium" : "low"),
        ...(d.details ? d.details(sample) : {}),
      });
  }
  candidates.sort((a, b) => b.signals.length - a.signals.length);
  return { best: candidates[0] || null, candidates };
}

export const KNOWN_OBFUSCATORS = DETECTORS.map(({ id, name, url, supported }) => ({ id, name, url, supported }));
