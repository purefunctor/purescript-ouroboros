import * as Diff from "diff";

export function diffPatchImpl(x, y) {
  return Diff.createTwoFilesPatch("old", "new", x, y);
}
