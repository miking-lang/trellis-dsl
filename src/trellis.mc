
include "parser/ast.mc"
include "parser/pprint.mc"
include "parser/resolve.mc"
include "model/ast.mc"
include "model/compile.mc"
include "model/convert.mc"
include "model/encode.mc"
include "model/entry.mc"
include "model/pprint.mc"
include "model/predecessors.mc"
include "build.mc"
include "trellis-arg.mc"

lang Trellis =
  TrellisAst + TrellisModelAst + TrellisModelConvert + TrellisCompileModel +
  TrellisEncode + TrellisPredecessors + TrellisGenerateViterbiEntry +
  TrellisGenerateHMMProgram + TrellisBuild
end

mexpr

use Trellis in

-- Parse command-line arguments
let result = argParse trellisDefaultOptions config in
match result with ParseOK r then
  let options : TrellisOptions = r.options in
  -- Exactly one file as argument?
  if neqi (length r.strings) 1 then
    -- No, print the menu and exit
    print (menu ());
    exit 0
  else
    -- Yes, read and parse the file
    let filename = head r.strings in

    -- Read the "parse" AST, the one generated by the syn tool.
    let p = parseTrellisExn filename (readFile filename) in
    (if options.printParse then
      printLn (use TrellisPrettyPrint in pprintTrellis p)
    else ());

    -- Construct the model AST, which is a simpler representation of the above
    -- AST.
    let modelAst = constructTrellisModelRepresentation p in
    (if options.printModel then
      printLn (use TrellisModelPrettyPrint in pprintTrellisModel modelAst)
    else ());

    -- Encodes state types as integers when in table accesses.
    let modelAst = encodeStateOperations options modelAst in

    -- Compile the Trellis model to Futhark, resulting in initializer code,
    -- definitions of the initial, output, and transition probabilities, as
    -- well and the compilation environment (to use later).
    let fut = compileTrellisModel options modelAst in

    -- If enabled, compute the predecessors of each state and write this to a
    -- file to be used at runtime. As this takes a long time to complete,
    -- because of an unoptimized implementation, this is currently disabled by
    -- default.
    -- OPT(larshum, 2024-01-30): Implement a more sophisticated approach which
    -- excludes "impossible" predecessors based on the conditions, to vastly
    -- improve the performance for most models (sparse models, in particular).
    (if options.computePredecessors then
      let preds = computePredecessors modelAst in
      writePredecessors options.outputDir preds
    else ());

    -- Generate a complete Futhark program by gluing together parts from the
    -- compilation results with pre-defined implemenentations of the core HMM
    -- algorithms (found under "src/skeleton").
    let prog = generateHMMProgram fut in

    -- Runs the building to produce a working Python wrapper which can be used
    -- to call the Futhark code.
    buildPythonWrapper fut.env prog
else
  argPrintError result;
  exit 1
