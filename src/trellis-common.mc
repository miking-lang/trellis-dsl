-- Contains definitions and functions shared among multiple files.

include "string.mc"
include "mexpr/info.mc"

let ppStrings = lam l. lam r.
  join ["   LHS: \"", l, "\"\n    RHS: \"", r, "\""]

let trellisInfo = lam id. infoVal id 0 0 0 0
