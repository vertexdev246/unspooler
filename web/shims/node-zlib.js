// Browser shim for the one Node zlib call the core makes:
// jsvirt.mjs decodes `base64 (+ zlib)` blobs with `zlib.inflateSync(buf)`
// when the payload carries the 0x78 0x9c zlib header.
import { unzlibSync } from "fflate";

export function inflateSync(buf) {
  const bytes = buf instanceof Uint8Array ? buf : new Uint8Array(buf);
  return unzlibSync(bytes);
}

export default { inflateSync };
