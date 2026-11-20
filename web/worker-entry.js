// Web Worker: runs the deobfuscator off the main thread. The input is only
// parsed and transformed with Babel — never executed.
import { deobfuscate } from "../src/deobf.mjs";
import { detectObfuscator } from "../src/detect.mjs";

self.onmessage = (e) => {
  const { code, options } = e.data || {};
  try {
    const started = performance.now();
    const detection = detectObfuscator(code);
    const r = deobfuscate(code, options || {});
    self.postMessage({
      ok: true,
      result: {
        code: r.code,
        strings: r.stats?.stringConcealing?.strings ?? [],
        stats: r.stats,
        errors: r.errors,
        detection,
        timeMs: Math.round(performance.now() - started),
      },
    });
  } catch (err) {
    const msg = err && err.message ? err.message : String(err);
    self.postMessage({ ok: false, error: "Could not parse input: " + msg });
  }
};
