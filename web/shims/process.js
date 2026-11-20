// Minimal `process` for the browser bundle. The core only ever reads
// `process.env.<DBG>` flags (all undefined here) to gate debug logging.
export default { env: {}, argv: [], platform: "browser" };
