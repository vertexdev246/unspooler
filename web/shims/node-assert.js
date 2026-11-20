// Browser shim for node's `assert` (only `ok` is used by the core).
export function ok(value, message) {
  if (!value) throw new Error(message || "Assertion failed");
}
export default ok;
