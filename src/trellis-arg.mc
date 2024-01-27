include "arg.mc"

type TrellisOptions = {
  batchSize : Int,
  batchOverlap : Int,
  useDoublePrecisionFloats : Bool,
  useBitsetEncoding : Bool,
  printParse : Bool,
  printModel : Bool
}

let trellisDefaultOptions = {
  batchSize = 1024,
  batchOverlap = 128,
  useDoublePrecisionFloats = false,
  useBitsetEncoding = false,
  printParse = false,
  printModel = false
}

let config = [
  ([("--batch-size", "", "<n>")],
    "Manually sets the size of each batch of input values processed in Viterbi",
    lam p.
      let o = p.options in {o with batchSize = argToIntMin p 1}),
  ([("--batch-overlap", "", "<n>")],
    "Manually sets the overlap to use between consecutive batches",
    lam p.
      let o = p.options in {o with batchOverlap = argToIntMin p 1}),
  ([("--use-double-precision", "", "")],
    "Use double-precision floating point numbers",
    lam p.
      let o = p.options in {o with useDoublePrecisionFloats = true}),
  ([("--use-bitset-encoding", "", "")],
    "Enables encoding of states using a bitset approach",
    lam p.
      let o = p.options in {o with useBitsetEncoding = true}),
  ([("--print-parse", "", "")],
    "Pretty-prints the parsed AST",
    lam p.
      let o = p.options in {o with printParse = true}),
  ([("--print-model", "", "")],
    "Pretty-prints the model AST after pre-processing the parsed AST",
    lam p.
      let o = p.options in {o with printModel = true})
]

let menu = lam. join [
  "Usage: trellis file.mc [<options>]\n\n",
  "Options:\n",
  argHelpOptions config,
  "\n"
]
