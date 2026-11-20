# Unspooler

**Unspooler** unwinds obfuscated JavaScript back into something you can read. Paste
obfuscated code in, get clean, formatted source out — it runs **entirely in your
browser**, so nothing is ever uploaded, and the input is only *parsed*, never executed.

> Live: **https://unspooler.pages.dev** · Deployed as a static site on Cloudflare Pages.

<p align="center"><em>Obfuscated in, readable out — no server, no upload.</em></p>

---

## What it reverses

Unspooler recognises the obfuscator from its fingerprint and applies the matching
passes. Supported today:

| Obfuscator | Coverage |
| --- | --- |
| **JS-Confuser** | Low / Medium / High presets — string encoding & concealing, control-flow flattening, opaque predicates, dispatcher, global/variable masking, pack, and more. |
| **javascript-obfuscator** (obfuscator.io) | Default → High — string array (rotation / base64 / RC4 / wrappers), control-flow switch flattening, dead-code, number & string transforms, self-defending. |
| **JSDefender** | Self-defending eval layers decrypted, constant/JSFuck helpers folded, switch-in-a-loop state machines rebuilt. |
| **Dean Edwards' packer** | `eval(function(p,a,c,k,e,d){…})` unpacked statically (all token encodings). |
| **JSFuck** | `[]()!+` programs parsed and recovered. |
| **jjencode / aaencode** | Symbol / kaomoji encodings decoded statically. |
| **jfogs**, **gnirts**, **js-virtualizer** | Decoded / lifted where the shape is proven. |

Everything is **shape-matched**: constructs that don't match a known obfuscator
template are left untouched, so Unspooler never guesses and never changes behaviour.

## How it works

The deobfuscator core is a set of Babel passes (`src/`). The browser build bundles
that core — unchanged — into a **Web Worker** with esbuild, shimming the handful of
Node built-ins it touches (`module.createRequire`, `node:zlib`, `Buffer`) for the
browser. The UI ([CodeMirror 6](https://codemirror.net/)) talks to the worker, so the
heavy AST work never blocks the page.

```
web/worker-entry.js ──▶ src/deobf.mjs (+ detect, cff, obfio, jsdefender, …)
web/main.js         ──▶ CodeMirror editors, worker wiring
build.mjs           ──▶ esbuild → dist/  (static, deployable anywhere)
```

## Develop

```bash
npm install
npm run dev      # builds + serves http://127.0.0.1:8788 (sourcemaps, unminified)
```

## Build

```bash
npm run build    # → dist/  (minified static site)
```

## Deploy to Cloudflare Pages

**Dashboard (Git integration):** connect this repo and set

- **Build command:** `npm run build`
- **Build output directory:** `dist`

**Wrangler (direct upload):**

```bash
npm run build
npx wrangler pages deploy dist --project-name unspooler
```

The output is fully static — it works on any static host (Pages, Netlify,
GitHub Pages, an S3 bucket).

## Safety

Unspooler **parses** input with Babel and rewrites the AST. It does **not** execute the
code it is given — encoders like JSFuck/packer are evaluated with a pure, sandboxed
sub-evaluator, never the real `eval`. All work happens client-side in a Web Worker.

## License

[MIT](LICENSE)
