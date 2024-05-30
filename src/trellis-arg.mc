include "arg.mc"
include "set.mc"
include "string.mc"

let defaultStr = lam defaultOptStr. lam msg.
  join [msg, " (default: ", defaultOptStr, ")"]

type TrellisOptions = {
  help : Bool,

  -- Configuration of batching used in the Viterbi algorithm.
  batchSize : Int,
  batchOverlap : Int,

  -- Options for trade-offs between performance and accuracy.
  useDoublePrecisionFloats : Bool,
  useFastMath : Bool,

  -- Controlling the predecessor analysis and whether to precompute the
  -- predecessors instead.
  warnPredecessorAnalysis : Bool,
  errorPredecessorAnalysis : Bool,
  forcePrecomputePredecessors : Bool,

  -- Debug parameters.
  printParse : Bool,
  printModel : Bool,

  outputDir : String
}

let trellisDefaultOptions = {
  help = false,
  batchSize = 1024,
  batchOverlap = 128,
  useDoublePrecisionFloats = false,
  useFastMath = false,
  warnPredecessorAnalysis = false,
  errorPredecessorAnalysis = false,
  forcePrecomputePredecessors = false,
  printParse = false,
  printModel = false,
  outputDir = "."
}

let _supportedFutharkTargets = setOfSeq cmpString [
  "c", "multicore", "cuda", "opencl"
]
let validateFutharkTarget = lam target.
  if setMem target _supportedFutharkTargets then target
  else
    let msg = join [
      "Futhark target '", target, "' is not supported\n",
      "Supported Futhark targets: ", strJoin " " (setToSeq _supportedFutharkTargets)
    ] in
    error msg

let config = [
  ([("--help", "", "")],
    "Show this menu.", lam p. let o = p.options in {o with help = true}),
  ([("--batch-size", " ", "<n>")],
    defaultStr (int2string trellisDefaultOptions.batchSize)
      "Manually sets the size of each batch of input values processed in Viterbi.",
    lam p.
      let o = p.options in {o with batchSize = argToIntMin p 0}),
  ([("--batch-overlap", " ", "<n>")],
    defaultStr (int2string trellisDefaultOptions.batchOverlap)
      "Manually sets the overlap to use between consecutive batches in Viterbi.",
    lam p.
      let o = p.options in {o with batchOverlap = argToIntMin p 0}),
  ([("--use-double-precision", "", "")],
    defaultStr (bool2string trellisDefaultOptions.useDoublePrecisionFloats)
      "Use double-precision (64-bit) floating point numbers.",
    lam p.
      let o = p.options in {o with useDoublePrecisionFloats = true}),
  ([("--use-fast-math", "", "")],
    defaultStr (bool2string trellisDefaultOptions.useFastMath)
      "Compiles the CUDA code with the '--use_fast_math' flag, to improve performance at the cost of losing accuracy.",
    lam p.
      let o = p.options in {o with useFastMath = true}),
  ([("--warn-predecessor-analysis", "", "")],
    defaultStr (bool2string trellisDefaultOptions.warnPredecessorAnalysis)
      "If enabled, the compiler warns if the predecessor analysis fails and prints the reason(s) why.",
    lam p.
      let o = p.options in {o with warnPredecessorAnalysis = true}),
  ([("--error-predecessor-analysis", "", "")],
    defaultStr (bool2string trellisDefaultOptions.errorPredecessorAnalysis)
      "If enabled, the compiler reports errors and exits with return code 1 if the predecessor analysis fails.",
    lam p.
      let o = p.options in {o with errorPredecessorAnalysis = true}),
  ([("--force-precompute-predecessors", "", "")],
    defaultStr (bool2string trellisDefaultOptions.forcePrecomputePredecessors)
      "If enabled, the compiler will always skip the predecessor analysis and precompute the predecessors at compile-time.",
    lam p.
      let o = p.options in {o with forcePrecomputePredecessors = true}),
  ([("--print-parse", "", "")],
    "Pretty-prints the initial AST after parsing.",
    lam p.
      let o = p.options in {o with printParse = true}),
  ([("--print-model", "", "")],
    "Pretty-prints the model AST after pre-processing the parsed AST.",
    lam p.
      let o = p.options in {o with printModel = true}),
  ([("--output-dir", " ", "<dir>")],
    defaultStr trellisDefaultOptions.outputDir
      "Specifies the name of a directory in which files should be placed.",
    lam p.
      let o = p.options in {o with outputDir = argToString p})
]

let menu = lam. join [
  "Usage: trellis [<options>] file.trellis\n\n",
  "Options:\n",
  argHelpOptions config,
  "\n"
]
