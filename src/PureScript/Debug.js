import * as util from "util";

export function _trace(x, k) {
  console.log(util.inspect(x, { depth: null, colors: true }));
  return k({});
}
