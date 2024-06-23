include "sys.mc"

include "src-loc.mc"
include "trellis-arg.mc"
include "model/encode.mc"
include "./cuda/ast.mc"
include "./cuda/compile.mc"
include "./cuda/pprint.mc"

lang TrellisGeneratePython =
  TrellisTypeCardinality + TrellisTypeBitwidth + TrellisCudaCompileBase

  sem indent : Int -> String
  sem indent =
  | n -> create (muli n 4) (lam. ' ')

  sem numpyType : TType -> String
  sem numpyType =
  | ty ->
    let n = bitwidthType ty in
    if lti n 8 then "np.uint8"
    else if lti n 16 then "np.uint16"
    else if lti n 32 then "np.uint32"
    else if lti n 64 then "np.uint64"
    else errorSingle [infoTTy ty] "Type bitwidth too large for a 64-bit value"

  sem ctypesType : TType -> String
  sem ctypesType =
  | ty ->
    let n = bitwidthType ty in
    if lti n 8 then "ctypes.c_uint8"
    else if lti n 16 then "ctypes.c_uint16"
    else if lti n 32 then "ctypes.c_uint32"
    else if lti n 64 then "ctypes.c_uint64"
    else errorSingle [infoTTy ty] "Type bitwidth too large for a 64-bit value"

  sem pythonBool : Bool -> String
  sem pythonBool =
  | true -> "True"
  | false -> "False"

  sem generatePythonWrapper : TrellisOptions -> Map Name TExpr -> TModel
                           -> CuCompileEnv -> String
  sem generatePythonWrapper options syntheticTables model =
  | env ->
    let numStates = cardinalityType model.stateType in
    let pyStateType = numpyType model.stateType in
    let pyCtypesStateType = ctypesType model.stateType in
    let pyObsType = numpyType model.outType in
    let pyCtypesObsType = ctypesType model.outType in
    let pyProbType =
      if options.useDoublePrecisionFloats then "np.float64"
      else "np.float32"
    in
    let pyCtypesProbType =
      if options.useDoublePrecisionFloats then "ctypes.c_double"
      else "ctypes.c_float"
    in
    let precompPred = pythonBool env.precomputedPredecessors in
    strJoin "\n" [
      join [indent 1, "def __init__(self, args):"],
      join [indent 2, "self.precompute_predecessors = ", precompPred],
      join [indent 2, "self.num_states = ", int2string numStates],
      join [indent 2, "self.num_preds = ", int2string (foldl addi 0 env.numPreds)],
      join [indent 2, "self.batch_size = ", int2string options.batchSize],
      join [indent 2, "self.batch_overlap = ", int2string options.batchOverlap],
      join [indent 2, "self.state_type = ", pyStateType],
      join [indent 2, "self.state_ctype = ", pyCtypesStateType],
      join [indent 2, "self.prob_type = ", pyProbType],
      join [indent 2, "self.prob_ctype = ", pyCtypesProbType],
      join [indent 2, "self.obs_type = ", pyObsType],
      join [indent 2, "self.obs_ctype = ", pyCtypesObsType],
      join [indent 2, "self.setup_library()"],
      join [indent 2, "self.copy_args(args)"],
      "",
      join [indent 1, "def copy_args(self, args):"],
      generateInitCall syntheticTables env model
    ]

  sem generateInitCall : Map Name TExpr -> CuCompileEnv -> TModel -> String
  sem generateInitCall syntheticTables env =
  | {tables = tables} ->
    let addDeclaredTableData = lam acc. lam tableId. lam tableTy.
      let tablePyType =
        match tableTy with TTable {args = !([]) & args} then
          "np.ctypeslib.ndpointer(dtype=self.prob_type, ndim=1, flags='C_CONTIGUOUS')"
        else
          "self.prob_ctype"
      in
      let tableValue =
        let id = nameGetStr tableId in
        -- Represent the table value differently depending on whether it is a
        -- scalar value or not.
        match tableTy with TTable {args = !([]) & args} then
          join ["np.array(args['", id, "'].flatten(), dtype=self.prob_type)"]
        else
          join ["float(args['", id, "'])"]
      in
      snoc acc (tablePyType, tableValue)
    in
    let addSyntheticTableData = lam acc. lam. lam expr.
      let tableValue = join ["float(", exprToPythonString expr, ")"] in
      snoc acc ("self.prob_ctype", tableValue)
    in
    let addPredecessorTableData = lam acc. lam i. lam.
      let id = concat "pred" (int2string i) in
      let tablePyType =
        "np.ctypeslib.ndpointer(dtype=self.state_type, ndim=1, flags='C_CONTIGUOUS')"
      in
      let tableValue = join [
        "np.array(np.load('./", id, ".npy').flatten(), dtype=self.state_type)"
      ] in
      snoc acc (tablePyType, tableValue)
    in
    let preds =
      if env.precomputedPredecessors then env.numPreds
      else []
    in
    let allTables : [(String, String)] =
      foldli
        addPredecessorTableData
        (mapFoldWithKey
          addSyntheticTableData
          (mapFoldWithKey addDeclaredTableData [] tables)
          syntheticTables)
        preds
    in
    let initArgTypesDecl = join [
      indent 2, "self.lib.init.argtypes = [\n",
      strJoin ",\n" (map (lam x. concat (indent 3) x.0) allTables),
      "\n", indent 2, "]"
    ] in
    let initArgCall = join [
      indent 2, "self.lib.init(", strJoin ", " (map (lam x. x.1) allTables), ")"
    ] in
    join [initArgTypesDecl, "\n", initArgCall]

  sem exprToPythonString : TExpr -> String
  sem exprToPythonString =
  | EBool t -> if t.b then "true" else "false"
  | EInt t -> int2string t.i
  | EProb t -> float2string (log t.p)
  | ETableAccess {table = table, args = []} ->
    join ["args['", nameGetStr table, "']"]
  | ETableAccess {table = table, args = [a]} ->
    join ["args['", nameGetStr table, "'][", exprToPythonString a, "]"]
  | EBinOp (t & {op = OAdd _ | OSub _ | OMul _ | ODiv _}) ->
    arithOpToPythonString t
  | EBinOp t ->
    join [
      "(", exprToPythonString t.lhs, " ", opToPythonString t.op, " ",
      exprToPythonString t.rhs, ")" ]
  | _ ->
    error "Internal error: Replaced non-constant body with synthetic table"

  sem arithOpToPythonString : BinOpRecord -> String
  sem arithOpToPythonString =
  | {op = op, lhs = lhs, rhs = rhs, ty = ty, info = info} ->
    let l = exprToPythonString lhs in
    let r = exprToPythonString rhs in
    match ty with TInt _ then
      join ["(", l, " ", opToPythonString op, " ", r, ")"]
    else match ty with TProb _ then
      match op with OAdd _ | OSub _ then
        join ["np.log(np.exp(", l, ") ", opToPythonString op, " np.exp(", r, "))"]
      else match op with OMul _ then
        join ["(", l, " ", opToPythonString (OAdd ()), " ", r, ")"]
      else
        join ["(", l, " ", opToPythonString (OSub ()), " ", r, ")"]
    else error "Internal error: Invalid type of arithmetic expression"

  sem opToPythonString : BOp -> String
  sem opToPythonString =
  | OAdd _ -> "+"
  | OSub _ -> "-"
  | OMul _ -> "*"
  | ODiv _ -> "/"
  | OMod _ -> "%"
  | OEq _ -> "=="
  | ONeq _ -> "!="
  | OLt _ -> "<"
  | OGt _ -> ">"
  | OLeq _ -> "<="
  | OGeq _ -> ">="
  | OAnd _ -> "and"
  | OOr _ -> "or"
end

lang TrellisBuild = TrellisCudaPrettyPrint + TrellisGeneratePython
  sem buildPythonLibrary : TrellisOptions -> Map Name TExpr -> TModel
                        -> CuProgram -> CuCompileEnv -> ()
  sem buildPythonLibrary options syntheticTables model cuProg =
  | env ->

    -- 1. Read the pre-defined CUDA skeleton containing efficient
    -- implementations of the algorithms we seek to use.
    let skeletonCode = readFile (concat trellisSrcLoc "skeleton/hmm.cu") in

    -- 2. Combine the model-specific generated CUDA program with the
    -- pre-defined skeleton and write the result to a file 'hmm.cu' in the
    -- output directory.
    let filePath = absPath options "hmm.cu" in
    writeFile filePath (concat (printCudaProgram cuProg) skeletonCode);

    -- 3. Compile the CUDA file to produce a shared library.
    compileCudaFile options filePath;

    -- 4. Read the pre-defined Python wrapper code.
    let wrapStr = readFile (concat trellisSrcLoc "skeleton/nvrtc-wrap.py") in

    -- 5. Generate the model-specific Python wrapper code and combine it with
    -- the skeleton code to produce a simple Python library in 'trellis.py'
    -- usable from other files.
    let trailStr = generatePythonWrapper options syntheticTables model env in
    writeFile (absPath options "trellis.py") (concat wrapStr trailStr)


  sem absPath : TrellisOptions -> String -> String
  sem absPath options =
  | file -> join [options.outputDir, "/", file]

  -- We compile the generated CUDA code to produce a shared library, which the
  -- Python wrapper code loads and uses at runtime.
  sem compileCudaFile : TrellisOptions -> String -> ()
  sem compileCudaFile options =
  | filePath ->
    let compileFlags = [
      "-O3", "-arch=native", "--shared", "-Xcompiler", "-fPIC", "-o",
      absPath options "libhmm.so", filePath
    ] in
    let compileFlags =
      if options.useFastMath then cons "--use_fast_math" compileFlags
      else compileFlags
    in
    let r = sysRunCommand (cons "nvcc" compileFlags) "" "." in
    if eqi r.returncode 0 then ()
    else
      let msg = join [
        "Compilation of generated CUDA code failed\n",
        "stdout: ", r.stdout, "\n",
        "stderr: ", r.stderr, "\n"
      ] in
      printError msg
end
