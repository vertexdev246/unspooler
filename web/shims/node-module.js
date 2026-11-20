// Browser shim for Node's `module.createRequire`.
//
// The deobfuscator core loads Babel through `createRequire(import.meta.url)`
// (so the same source runs under Node without a build step). In the browser
// bundle there is no runtime `require`, so we resolve those exact specifiers to
// the Babel modules esbuild has already bundled. Nothing else is requireable.
import * as babelParser from "@babel/parser";
import * as babelTraverse from "@babel/traverse";
import * as babelGenerate from "@babel/generator";
import * as babelTypes from "@babel/types";

const MAP = {
  "@babel/parser": babelParser,
  "@babel/traverse": babelTraverse,
  "@babel/generator": babelGenerate,
  "@babel/types": babelTypes,
  // Referenced only by a JSDDBG2 debug branch that never runs in the browser.
  fs: { appendFileSync() {} },
};

export function createRequire() {
  return (id) => {
    if (id in MAP) return MAP[id];
    throw new Error("Unspool browser bundle: cannot require('" + id + "')");
  };
}

export default { createRequire };
