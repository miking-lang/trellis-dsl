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

  sem numpyTypeSize : TType -> String
  sem numpyTypeSize =
  | ty ->
    let n = bitwidthType ty in
    if lti n 8 then "np.uint8"
    else if lti n 16 then "np.uint16"
    else if lti n 32 then "np.uint32"
    else if lti n 64 then "np.uint64"
    else errorSingle [infoTTy ty] "Type bitwidth too large for a 64-bit value"

  sem generatePythonWrapper : TrellisOptions -> Map Name TExpr -> TModel
                           -> CuCompileEnv -> String
  sem generatePythonWrapper options syntheticTables model =
  | env ->
    let numStates = cardinalityType model.stateType in
    let pyStateType = numpyTypeSize model.stateType in
    let pyObsType = numpyTypeSize model.outType in
    let pyProbType =
      if options.useDoublePrecisionFloats then "np.float64"
      else "np.float32"
    in
    let precompPred =
      if env.precomputedPredecessors then "True"
      else "False"
    in
    strJoin "\n" [
      join [indent 1, "def __init__(self, args):"],
      join [indent 2, "self.precompute_predecessors = ", precompPred],
      join [indent 2, "self.num_states = ", int2string numStates],
      join [indent 2, "self.num_preds = ", int2string env.numPreds],
      join [indent 2, "self.batch_size = ", int2string options.batchSize],
      join [indent 2, "self.batch_overlap = ", int2string options.batchOverlap],
      join [indent 2, "self.state_type = ", pyStateType],
      join [indent 2, "self.prob_type = ", pyProbType],
      join [indent 2, "self.obs_type = ", pyObsType],
      join [indent 2, "self.compile_cuda('hmm.cu')"],
      join [indent 2, "self.copy_args(args)"],
      "",
      join [indent 1, "def __del__(self):"],
      generateFreeTables model,
      join [indent 2, "if hasattr(self, 'module'):"],
      join [indent 3, "err, = cuda.cuModuleUnload(self.module)"],
      join [indent 3, "cuda_check(err)"],
      join [indent 2, "if hasattr(self, 'ctx'):"],
      join [indent 3, "err, = cuda.cuCtxDestroy(self.ctx)"],
      join [indent 3, "cuda_check(err)"],
      "",
      join [indent 1, "def copy_args(self, args):"],
      generateCopyToGpuTables syntheticTables env model
    ]

  sem getTableField : Name -> String
  sem getTableField =
  | tableId -> concat "tables_" (nameGetStr tableId)

  -- Generates code for deallocating a table field in the Python wrapper.
  sem deallocTable : Name -> String
  sem deallocTable =
  | tableId ->
    let tid = getTableField tableId in
    strJoin "\n" [
      join [indent 2, "if hasattr(self, '", tid, "'):"],
      join [indent 3, "err, = cuda.cuMemFree(self.", tid, ")"],
      join [indent 3, "cuda_check(err)"]
    ]

  -- Generate code to deallocate the GPU data of all tables of the given model.
  sem generateFreeTables : TModel -> String
  sem generateFreeTables =
  | {tables = tables} ->
    let frees =
      mapFoldWithKey
        (lam acc. lam id. lam ty.
          match ty with TTable {args = !([]) & args} then
            snoc acc (deallocTable id)
          else acc)
        [] tables
    in
    strJoin "\n" frees

  sem flattenTable : Name -> String
  sem flattenTable =
  | tableId ->
    let str = nameGetStr tableId in
    join [indent 2, "args['", str, "'] = args['", str, "'].flatten()"]

  sem copyTableToGpu : Name -> String
  sem copyTableToGpu =
  | tableId ->
    let tid = getTableField tableId in
    let str = nameGetStr tableId in
    join [
      indent 2, "self.", tid, " = self.copy_to_gpu(np.array(args['", str,
      "'], dtype=self.prob_type), 0)" ]

  -- Generate code to copy the data of all tables of the given model to the
  -- GPU.
  sem generateCopyToGpuTables : Map Name TExpr -> CuCompileEnv -> TModel -> String
  sem generateCopyToGpuTables syntheticTables env =
  | {tables = tables} ->
    -- Code for flattening tables and copying them to the GPU. Single element
    -- tables are converted to NumPy arrays instead.
    -- NOTE(larshum, 2024-05-08): For simplicity, we assume all tables contain
    -- probabilities.
    let copies =
      let copiesStrs =
        mapFoldWithKey
          (lam acc. lam id. lam ty.
            let tid = getTableField id in
            match ty with TTable {args = !([]) & args} then
              snoc acc (strJoin "\n" [flattenTable id, copyTableToGpu id])
            else
              snoc acc (join [
                indent 2, "self.", tid, " = np.array(args['", nameGetStr id,
                "'], dtype=self.prob_type)" ]) )
          [] tables
      in
      strJoin "\n" copiesStrs
    in
    -- Construct the synthetic tables based on the tables provided as
    -- arguments.
    let syntheticTablesStr =
      strJoin "\n"
        (mapFoldWithKey
          (lam acc. lam id. lam expr.
            let tid = getTableField id in
            snoc acc (join [
              indent 2, "self.", tid, " = np.array(", exprToPythonString expr,
              ", dtype=self.prob_type)" ]))
          [] syntheticTables)
    in
    let predecessorsStr =
      if env.precomputedPredecessors then
        join [
          indent 2, "self.predecessors = ",
          "np.load(f'./predecessors.npy').transpose().flatten()\n",
          indent 2, "self.predecessors = ",
          "self.copy_to_gpu(np.array(self.predecessors, dtype=self.state_type), 0)"
        ]
      else ""
    in
    -- Construct the list of table pointers which are passed to CUDA kernels
    -- when launching them.
    let tablePtrs =
      let tablePtrsStr =
        mapFoldWithKey
          (lam acc. lam id. lam ty.
            let tid = getTableField id in
            match ty with TTable {args = !([]) & args} then
              snoc acc
                (join [indent 3, "np.array([int(self.", tid, ")], dtype=np.uint64),"])
            else
              snoc acc (join [indent 3, "self.", tid, ","]))
          [] tables
      in
      -- We add the synthetic tables to the back of the list
      let tablePtrsStr =
        mapFoldWithKey
          (lam acc. lam id. lam.
            let tid = getTableField id in
            snoc acc (join [indent 3, "self.", tid, ","]))
          tablePtrsStr syntheticTables
      in
      let tablePtrsStr =
        if env.precomputedPredecessors then
          concat tablePtrsStr ["np.array([int(self.predecessors)], dtype=np.uint64)"]
        else tablePtrsStr
      in
      strJoin "\n" [
        join [indent 2, "self.table_ptrs = ["],
        strJoin "\n" tablePtrsStr,
        join [indent 2, "]"]
      ]
    in
    join [copies, "\n", syntheticTablesStr, "\n", predecessorsStr, "\n", tablePtrs]

  sem exprToPythonString : TExpr -> String
  sem exprToPythonString =
  | EBool t -> if t.b then "true" else "false"
  | EInt t -> int2string t.i
  | EProb t -> float2string (log t.p)
  | ETableAccess {table = table, args = []} ->
    join ["args['", nameGetStr table, "']"]
  | ETableAccess {table = table, args = [a]} ->
    join ["args['", nameGetStr table, "'][", exprToPythonString a, "]"]
  | EIf t ->
    join [
      exprToPythonString t.thn, " if ", exprToPythonString t.cond, " else ",
      exprToPythonString t.els ]
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
    let absPath = lam file. join [options.outputDir, "/", file] in

    -- 1. Read the pre-defined CUDA skeleton containing efficient
    -- implementations of the algorithms we seek to use.
    let skeletonCode = readFile (concat trellisSrcLoc "skeleton/hmm.cu") in

    -- 2. Combine the model-specific generated CUDA program with the
    -- pre-defined skeleton and write the result to a file 'hmm.cu' in the
    -- output directory.
    let filePath = absPath "hmm.cu" in
    writeFile filePath (concat (printCudaProgram cuProg) skeletonCode);

    -- 3. Read the pre-defined Python wrapper code.
    let wrapStr = readFile (concat trellisSrcLoc "skeleton/nvrtc-wrap.py") in

    -- 4. Generate the model-specific Python wrapper code and combine it with
    -- the skeleton code to produce a simple Python library in 'trellis.py'
    -- usable from other files.
    let trailStr = generatePythonWrapper options syntheticTables model env in
    writeFile (absPath "trellis.py") (concat wrapStr trailStr)
end
