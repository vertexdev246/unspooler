// Builds the static site into dist/. Pure client-side: the deobfuscator core
// is bundled (unchanged) into a module Web Worker; Node built-ins it reaches
// for (module.createRequire, node:zlib, Buffer, process) are shimmed for the
// browser. Output is static files deployable to Cloudflare Pages.
import * as esbuild from "esbuild";
import { fileURLToPath } from "url";
import path from "path";
import fs from "fs";
import http from "http";

const root = path.dirname(fileURLToPath(import.meta.url));
const dist = path.join(root, "dist");
const assets = path.join(dist, "assets");
const serve = process.argv.includes("--serve");

const shim = (p) => path.join(root, "web", "shims", p);

/** shared bundle settings */
const common = {
  bundle: true,
  format: "esm",
  platform: "browser",
  target: ["es2022"],
  legalComments: "none",
  logLevel: "info",
  alias: {
    module: shim("node-module.js"),
    "node:module": shim("node-module.js"),
    zlib: shim("node-zlib.js"),
    "node:zlib": shim("node-zlib.js"),
    assert: shim("node-assert.js"),
    "node:assert": shim("node-assert.js"),
  },
  inject: [shim("globals-inject.js")],
  define: { "process.env.NODE_ENV": '"production"' },
};

async function build() {
  fs.rmSync(dist, { recursive: true, force: true });
  fs.mkdirSync(assets, { recursive: true });

  await esbuild.build({
    ...common,
    entryPoints: { worker: path.join(root, "web", "worker-entry.js") },
    outdir: assets,
    minify: !serve,
    sourcemap: serve,
  });

  await esbuild.build({
    ...common,
    entryPoints: { main: path.join(root, "web", "main.js") },
    outdir: assets,
    minify: !serve,
    sourcemap: serve,
  });

  // static files
  for (const f of ["index.html", "style.css", "favicon.svg"]) {
    const from = path.join(root, "web", f);
    if (fs.existsSync(from)) fs.copyFileSync(from, path.join(dist, f));
  }
  // Cloudflare Pages SPA-ish niceties
  fs.writeFileSync(path.join(dist, "_headers"), "/assets/*\n  Cache-Control: public, max-age=31536000, immutable\n");

  console.log("built → dist/");
}

await build();

if (serve) {
  const MIME = { ".html": "text/html", ".js": "text/javascript", ".css": "text/css", ".svg": "image/svg+xml", ".map": "application/json" };
  const port = 8788;
  http
    .createServer((req, res) => {
      let rel = decodeURIComponent(new URL(req.url, "http://x").pathname);
      if (rel === "/") rel = "/index.html";
      const file = path.join(dist, rel);
      if (!file.startsWith(dist)) { res.writeHead(403); return res.end("forbidden"); }
      fs.readFile(file, (err, data) => {
        if (err) { res.writeHead(404); return res.end("not found"); }
        res.writeHead(200, { "Content-Type": MIME[path.extname(file)] || "application/octet-stream" });
        res.end(data);
      });
    })
    .listen(port, "127.0.0.1", () => console.log(`dev → http://127.0.0.1:${port}`));
}
