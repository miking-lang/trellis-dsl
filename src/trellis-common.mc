-- Contains definitions and functions shared among multiple files.

include "name.mc"
include "string.mc"
include "utest.mc"
include "mexpr/info.mc"

let ppStrings = lam l. lam r.
  let ppStr = lam x. join ["\"", x, "\""] in
  utestDefaultToString ppStr ppStr l r

let trellisInfo = lam id. infoVal id 0 0 0 0

let generatedFileName = "generated"
let predecessorsFileName = "predecessors.txt"
