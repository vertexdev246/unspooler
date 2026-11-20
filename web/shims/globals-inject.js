// Globals esbuild injects into every bundled module:
//  - Buffer: jsvirt.mjs uses `Buffer.from(text, "base64")`.
//  - process: the core reads `process.env.<DBG>` flags (all undefined here).
import { Buffer } from "buffer";
export { Buffer };
export { default as process } from "./process.js";
