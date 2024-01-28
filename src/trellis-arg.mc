include "arg.mc"
include "string.mc"

let defaultStr = lam defaultOptStr. lam msg.
  join [msg, " (default: ", defaultOptStr, ")"]

type TrellisOptions = {
  batchSize : Int,
  batchOverlap : Int,
  useDoublePrecisionFloats : Bool,
  useBitsetEncoding : Bool,
  printParse : Bool,
  printModel : Bool,
  outputDir : String,
  futharkTarget : String
}

let trellisDefaultOptions = {
  batchSize = 1024,
  batchOverlap = 128,
  useDoublePrecisionFloats = false,
  useBitsetEncoding = false,
  printParse = false,
  printModel = false,
  outputDir = "build",
  futharkTarget = "multicore"
}

let config = [
  ([("--batch-size", " ", "<n>")],
    defaultStr (int2string trellisDefaultOptions.batchSize)
      "Manually sets the size of each batch of input values processed in Viterbi",
    lam p.
      let o = p.options in {o with batchSize = argToIntMin p 1}),
  ([("--batch-overlap", " ", "<n>")],
    defaultStr (int2string trellisDefaultOptions.batchOverlap)
      "Manually sets the overlap to use between consecutive batches",
    lam p.
      let o = p.options in {o with batchOverlap = argToIntMin p 1}),
  ([("--use-double-precision", "", "")],
    defaultStr (bool2string trellisDefaultOptions.useDoublePrecisionFloats)
      "Use double-precision floating point numbers",
    lam p.
      let o = p.options in {o with useDoublePrecisionFloats = true}),
  ([("--use-bitset-encoding", "", "")],
    defaultStr (bool2string trellisDefaultOptions.useBitsetEncoding)
      "Enables encoding of states using a bitset approach",
    lam p.
      let o = p.options in {o with useBitsetEncoding = true}),
  ([("--print-parse", "", "")],
    "Pretty-prints the initial AST after parsing",
    lam p.
      let o = p.options in {o with printParse = true}),
  ([("--print-model", "", "")],
    "Pretty-prints the model AST after pre-processing the parsed AST",
    lam p.
      let o = p.options in {o with printModel = true}),
  ([("--output-dir", " ", "<dir>")],
    defaultStr trellisDefaultOptions.outputDir
      "Specifies the name of a directory in which files should be placed",
    lam p.
      let o = p.options in {o with outputDir = argToString p}),
  ([("--futhark-target", " ", "<target>")],
    defaultStr trellisDefaultOptions.futharkTarget
      "Specifies the target backend to use when compiling Futhark",
    lam p.
      let o = p.options in {o with futharkTarget = argToString p})
]

let menu = lam. join [
  "Usage: trellis [<options>] file.trellis\n\n",
  "Options:\n",
  argHelpOptions config,
  "\n"
]
