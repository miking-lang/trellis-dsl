-- Contains definitions and functions shared among multiple files.

include "error.mc"
include "name.mc"
include "string.mc"
include "utest.mc"
include "mexpr/info.mc"

let printSection : Bool -> [Info] -> String -> String =
  lam warning. lam infos. lam msg.
  let section = {errorDefault with msg = msg, infos = infos} in
  match errorMsg [section] {single = "", multi = ""} with (i, msg) in
  if warning then infoWarningString i msg
  else infoErrorString i msg

let ppStrings = lam l. lam r.
  let ppStr = lam x. join ["\"", x, "\""] in
  utestDefaultToString ppStr ppStr l r

let trellisInfo = lam id. infoVal id 0 0 0 0
