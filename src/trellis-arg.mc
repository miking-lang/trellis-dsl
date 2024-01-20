include "arg.mc"

type TrellisOptions = {
  useDoublePrecisionFloats : Bool,
  prettyPrint : Bool,
  printAfterSimplification : Bool
}

let trellisDefaultOptions = {
  useDoublePrecisionFloats = false,
  prettyPrint = false,
  printAfterSimplification = false
}

let config = [
  ([("--use-double-precision", "", "")],
    "Use double-precision floating point numbers",
    lam p.
      let o = p.options in {o with useDoublePrecisionFloats = true}),
  ([("--pretty-print", "", "")],
    "Pretty-prints the AST after parsing",
    lam p.
      let o = p.options in {o with prettyPrint = true}),
  ([("--print-simplify", "", "")],
    "Pretty-prints the AST after running a simplfication pass",
    lam p.
      let o = p.options in {o with printAfterSimplification = true})
]

let menu = lam. join [
  "Usage: trellis file.mc [<options>]\n\n",
  "Options:\n",
  argHelpOptions config,
  "\n"
]
