include "sys.mc"

include "src-loc.mc"
include "trellis-arg.mc"
include "model/encode.mc"
include "./cuda/ast.mc"
include "./cuda/pprint.mc"

lang TrellisGeneratePython = TrellisTypeCardinality + TrellisTypeBitwidth
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

  sem generatePythonWrapper : TrellisOptions -> TModel -> String
  sem generatePythonWrapper options =
  | model ->
    let numStates = cardinalityType model.stateType in
    let pyStateType = numpyTypeSize model.stateType in
    let pyObsType = numpyTypeSize model.outType in
    let pyProbType =
      if options.useDoublePrecisionFloats then "np.float64"
      else "np.float32"
    in
    strJoin "\n" [
      join [indent 1, "def __init__(self, args):"],
      join [indent 2, "self.num_states = ", int2string numStates],
      join [indent 2, "self.batch_size = ", int2string options.batchSize],
      join [indent 2, "self.batch_overlap = ", int2string options.batchOverlap],
      join [indent 2, "self.state_type = ", pyStateType],
      join [indent 2, "self.prob_type = ", pyProbType],
      join [indent 2, "self.obs_type = ", pyObsType],
      join [indent 2, "self.compile_cuda('hmm.cu')"],
      join [indent 2, "self.copy_args(args)"],
      join [indent 1, "def __del__(self):"],
      generateFreeTables model,
      join [indent 2, "if hasattr(self, 'module'):"],
      join [indent 3, "err, = cuda.cuModuleUnload(self.module)"],
      join [indent 3, "cuda_check(err)"],
      join [indent 2, "if hasattr(self, 'ctx'):"],
      join [indent 3, "err, = cuda.cuCtxDestroy(self.ctx)"],
      join [indent 3, "cuda_check(err)"],
      join [indent 1, "def copy_args(self, args):"],
      generateCopyToGpuTables model
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
  sem generateCopyToGpuTables : TModel -> String
  sem generateCopyToGpuTables =
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
      strJoin "\n" [
        join [indent 2, "self.table_ptrs = ["],
        strJoin "\n" tablePtrsStr,
        join [indent 2, "]"]
      ]
    in
    join [copies, "\n", tablePtrs]
end

lang TrellisBuild = TrellisCudaPrettyPrint + TrellisGeneratePython
  sem buildPythonLibrary : TrellisOptions -> TModel -> CuProgram -> ()
  sem buildPythonLibrary options model =
  | cuProg ->
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
    let pythonWrapper = readFile (concat trellisSrcLoc "skeleton/nvrtc-wrap.py") in

    -- 4. Generate the model-specific Python wrapper code and combine it with
    -- the skeleton code to produce a simple Python library in 'trellis.py'
    -- usable from other files.
    writeFile (absPath "trellis.py")
      (concat pythonWrapper (generatePythonWrapper options model));

    -- 5. Create an empty file '__init__.py' to allow calling the generated
    -- Python library from another directory.
    writeFile (absPath "__init__.py") ""
end
