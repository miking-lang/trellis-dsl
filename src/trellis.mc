
include "parser/ast.mc"
include "parser/pprint.mc"
include "parser/resolve.mc"
include "model/ast.mc"
include "model/compile.mc"
include "model/convert.mc"
include "model/encode.mc"
include "model/generate-predecessors.mc"
include "model/merge-subseq-ops.mc"
include "model/pprint.mc"
include "model/predecessors.mc"
include "model/reduce-tables.mc"
include "build.mc"
include "entry-points.mc"
include "trellis-arg.mc"

lang Trellis =
  TrellisAst + TrellisModelAst + TrellisModelConvert + TrellisGeneratePredecessors +
  TrellisCompileModel + TrellisReduceTableDimensionality + TrellisEncode +
  TrellisModelMergeSubsequentOperations + TrellisGenerateHMMProgram +
  TrellisBuild
end

mexpr

use Trellis in

let result = argParse trellisDefaultOptions config in
match result with ParseOK r then
  let options : TrellisOptions = r.options in
  if neqi (length r.strings) 1 then
    print (menu ());
    exit 0
  else
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

    -- Simplify the model by reducing the dimension of all tables to one and
    -- transforming the model accordingly.
    let modelAst = reduceTableDimensionalityModel modelAst in

    -- Merge subsequent operations on the same tuple in set constraints to
    -- reduce the number of comparisons.
    let modelAst = mergeSubsequentOperationsModel modelAst in

    -- Encodes state types as integers when in table accesses.
    let modelAst = encodeStateOperations options modelAst in

    (if options.printTransformedModel then
      printLn (use TrellisModelPrettyPrint in pprintTrellisModel modelAst)
    else ());

    -- Produces a compilation environment which we use to accumulate
    -- information through later passes.
    let env = initCompileEnv options modelAst in

    -- Attempt to compute the predecessors, unless the programmer explicitly
    -- asks the compiler not to.
    let env =
      if options.skipPredecessors then env
      else computePredecessors env modelAst
    in

    -- Compile the Trellis model to Futhark, producing the initializer,
    -- definitions of the probability functions, as well as the compilation
    -- environment.
    let fut = compileTrellisModel env modelAst in

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
