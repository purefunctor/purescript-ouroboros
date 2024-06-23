import * as util from "util";

export function inspectImpl(x) {
  return util.inspect(x, { depth: null, colors: true });
}

export function _trace(x, k) {
  console.log(util.inspect(x, { depth: null, colors: true }));
  return k({});
}
