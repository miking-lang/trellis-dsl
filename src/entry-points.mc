-- Generates the Futhark entry points for the various algorithms to apply to a
-- HMM. We provide multiple entry points to certain algorithms to maximize
-- performance in different situations.

include "mexpr/info.mc"

include "model/compile.mc"
include "src-loc.mc"

-- The names of the pre-defined functions in the skeleton code which we glue
-- together with our generated code.
let viterbiFirstBatchId = nameSym "viterbi_first_batch"
let viterbiSubseqBatchId = nameSym "viterbi_subseq_batch"
let forwardHelperId = nameSym "forward_helper"
let logSumExpId = nameSym "log_sum_exp"

let viterbiEntryId = nameSym "viterbi"
let forwardEntryId = nameSym "forward"

let i = infoVal "trellis-generated" 0 0 0 0

let n = nameSym "n"
let m = nameSym "m"
let k = nameSym "k"
let predecessorsId = nameSym "predecessors"
let inputsId = nameSym "inputSignals"
let inputLengthsId = nameSym "inputLengths"

lang TrellisGenerateEntry = TrellisCompileModel + FutharkAst
  type FutFunArgs = [(Name, FutType)]

  sem stateI64 : FutExpr -> FutExpr
  sem stateI64 =
  | e ->
    futApp_ (futProj_ (nFutVar_ stateModuleId) "i64") e

  sem generateHigherOrderProbabilityFunctions : TrellisCompileEnv -> (FutExpr, [Name])
  sem generateHigherOrderProbabilityFunctions =
  | env ->
    let initId = nameSym "initp" in
    let outId = nameSym "outp" in
    let transId = nameSym "transp" in
    let probFunIds = [initId, outId, transId] in
    let probFunDeclExpr =
      if env.precomputeTables then
        let initExpr =
          generateTableAccess initId "init" [("x", stateModuleId)]
        in
        let outExpr =
          generateTableAccess outId "out" [("x", stateModuleId), ("o", obsModuleId)]
        in
        let transExpr =
          generateTableAccess transId "trans" [("x", stateModuleId), ("y", stateModuleId)]
        in
        futBindall_ [initExpr, outExpr, transExpr]
      else
        let initExpr =
          generateHigherOrderProbabilityFunction
            initId initialProbabilityId [nameNoSym "x"]
        in
        let outExpr =
          generateHigherOrderProbabilityFunction
            outId outputProbabilityId [nameNoSym "x", nameNoSym "o"]
        in
        let transExpr =
          generateHigherOrderProbabilityFunction
            transId transitionProbabilityId [nameNoSym "x", nameNoSym "y"]
        in
        futBindall_ [initExpr, outExpr, transExpr]
    in
    (probFunDeclExpr, probFunIds)

  sem generateTableAccess : Name -> String -> [(String, Name)] -> FutExpr
  sem generateTableAccess id field =
  | args ->
    let arrayAccess = lam acc. lam arg.
      futArrayAccess_ acc
        (futApp_ (futProj_ (nFutVar_ arg.1) "to_i64") (futVar_ arg.0))
    in
    let access =
      foldl arrayAccess (futProj_ (nFutVar_ modelId) field) args
    in
    nuFutLet_ id (foldr futLam_ access (map (lam a. a.0) args))

  sem generateHigherOrderProbabilityFunction : Name -> Name -> [Name] -> FutExpr
  sem generateHigherOrderProbabilityFunction id mainDefId =
  | mainArgIds ->
    let argIds = cons modelId mainArgIds in
    let body = futAppSeq_ (nFutVar_ mainDefId) (map nFutVar_ argIds) in
    nuFutLet_ id (foldr nFutLam_ body mainArgIds)

  sem arrayTy : Name -> [Option FutArrayDim] -> FutType
  sem arrayTy tyId =
  | dims ->
    let buildArrayType = lam acc. lam dim.
      FTyArray { elem = acc, dim = dim, info = i }
    in
    let ty = FTyIdent {ident = tyId, info = i} in
    foldl buildArrayType ty dims
end

lang TrellisGenerateViterbiEntry = TrellisGenerateEntry
  sem generateViterbiEntryPoint : TrellisCompileEnv -> FutDecl
  sem generateViterbiEntryPoint =
  | env ->
    let params =
      [ (modelId, FTyIdent {ident = modelTyId, info = i})
      , (predecessorsId, arrayTy stateTyId [None (), Some (NamedDim nstatesId)])
      , (inputsId, arrayTy obsTyId [Some (NamedDim m), Some (NamedDim n)]) ]
    in
    let retTy = arrayTy stateTyId [None (), Some (NamedDim n)] in
    match generateHigherOrderProbabilityFunctions env with (expr, probFunIds) in
    let body = futBind_ expr (generateViterbiBatchingMap env probFunIds) in
    FDeclFun {
      ident = viterbiEntryId, entry = true,
      typeParams = [FPSize {val = n}, FPSize {val = m}], params = params,
      ret = retTy, body = body, info = i}

  sem generateViterbiBatchingMap : TrellisCompileEnv -> [Name] -> FutExpr
  sem generateViterbiBatchingMap env =
  | probFunIds ->
    let batchOutputSize = subi env.options.batchSize env.options.batchOverlap in
    let bosExpr = futInt_ batchOutputSize in
    let nbatchesExpr =
      futDiv_ (futSub_ (nFutVar_ m) (futInt_ env.options.batchOverlap)) bosExpr
    in
    let nbatchesId = nameSym "nbatches" in
    let nbatches = nFutVar_ nbatchesId in
    let outputSize = nameSym "outputSize" in
    let signalId = nameSym "signal" in
    let batchesId = nameSym "batches" in
    let prevStateId = nameSym "prev_state" in
    let ofsId = nameSym "ofs" in
    let signalOutType = futSizedArrayTy_ (nFutIdentTy_ stateTyId) outputSize in
    let viterbiFstBatch = futAppSeq_ (nFutVar_ viterbiFirstBatchId) (join [
      [nFutVar_ predecessorsId],
      map nFutVar_ probFunIds,
      [futArraySlice_ (nFutVar_ signalId) (futInt_ 0) (futInt_ env.options.batchSize)]
    ]) in
    let viterbiSubseqBatch = futAppSeq_ (nFutVar_ viterbiSubseqBatchId) (join [
      [nFutVar_ predecessorsId],
      map nFutVar_ (subsequence probFunIds 1 (length probFunIds)),
      [ nFutVar_ prevStateId
      , futArraySlice_ (nFutVar_ signalId) (nFutVar_ ofsId)
          (futAdd_ (nFutVar_ ofsId) (futInt_ env.options.batchSize)) ]
    ]) in
    let loopParam = (nFutPvar_ batchesId, nFutVar_ batchesId) in
    let idxId = nameSym "i" in
    let nextIdx = futAdd_ (nFutVar_ idxId) (futInt_ 1) in
    let outId = nameSym "out" in
    let batchLoop =
      futForEach_ loopParam idxId
        (futIota_ (futSub_ nbatches (futInt_ 1)))
        (futBindall_ [
          nuFutLet_ ofsId
            (futMul_ nextIdx (futInt_ batchOutputSize)),
          nuFutLet_ prevStateId (
            futArrayAccess_
              (futArrayAccess_ (nFutVar_ batchesId) (nFutVar_ idxId))
              (futInt_ (subi batchOutputSize 1))),
          nuFutLet_ outId viterbiSubseqBatch,
          futArrayUpdate_ (nFutVar_ batchesId) nextIdx (
            futArraySlice_ (nFutVar_ outId) (futInt_ 0)
              (futInt_ batchOutputSize))
        ])
    in
    let mapBody = futBindall_ [
      nuFutLet_ batchesId (
        futTabulate_ (nFutVar_ nbatchesId) (futLam_ ""
          (futTabulate_ (futInt_ batchOutputSize) (futLam_ ""
            (futApp_ (futProj_ (nFutVar_ stateModuleId) "i64") (futInt_ 0)))))),
      nuFutLet_ batchesId (
        futArraySlice_
          (futArrayUpdate_ (nFutVar_ batchesId) (futInt_ 0) viterbiFstBatch)
          (futInt_ 0) (futInt_ batchOutputSize)),
      nuFutLet_ batchesId batchLoop,
      futSizeCoercion_ (futFlatten_ (nFutVar_ batchesId)) signalOutType
    ] in
    futBindall_ [
      nuFutLet_  nbatchesId
        (futDiv_ (futSub_ (nFutVar_ m) (futInt_ env.options.batchOverlap))
          (futInt_ batchOutputSize)),
      nuFutLet_ outputSize (futMul_ nbatches (futInt_ batchOutputSize)),
      futMap_ (nFutLam_ signalId mapBody) (nFutVar_ inputsId)
    ]
end

lang TrellisGenerateForwardEntry = TrellisGenerateEntry
  sem generateForwardEntryPoint : TrellisCompileEnv -> FutDecl
  sem generateForwardEntryPoint =
  | env ->
    match generateHigherOrderProbabilityFunctions env with (expr, probFunIds) in
    let forwardArgs =
      cons
        (nFutVar_ predecessorsId)
        (map nFutVar_ probFunIds)
    in
    let tables = mapBindings env.tables in
    generateForwardEntry tables expr forwardArgs

  sem generateForwardEntry : [(Name, FutType)] -> FutExpr -> [FutExpr] -> FutDecl
  sem generateForwardEntry tables probDeclExpr =
  | forwardArgs ->
    let inputLengthsType = FTyArray {
      elem = FTyInt {sz = I64 (), info = i}, dim = Some (NamedDim n), info = i
    } in
    let params =
      [ (modelId, nFutIdentTy_ modelTyId)
      , (predecessorsId, arrayTy stateTyId [Some (NamedDim npredsId), Some (NamedDim nstatesId)])
      , (inputsId, arrayTy obsTyId [None (), Some (NamedDim n)]) ]
    in
    let retTy = arrayTy probTyId [Some (NamedDim n)] in
    let body = futBind_
      probDeclExpr
      (futMap_
        (futAppSeq_ (nFutVar_ forwardHelperId) forwardArgs)
        (nFutVar_ inputsId))
    in
    FDeclFun {
      ident = forwardEntryId, entry = true,
      typeParams = [FPSize {val = n}], params = params,
      ret = retTy, body = body, info = i}
end

lang TrellisGenerateHMMProgram =
  TrellisGenerateViterbiEntry + TrellisGenerateForwardEntry +
  FutharkPrettyPrint

  sem generateHMMProgram : TrellisCompileOutput -> String
  sem generateHMMProgram =
  | {env = env, initializer = init} ->
    let viterbi = generateViterbiEntryPoint env in
    let forward = generateForwardEntryPoint env in
    let pregenCode = readFile (concat trellisSrcLoc "skeleton/hmm.fut") in
    let trailingCode = FProg { decls = [viterbi, forward] } in
    strJoin "\n" [printFutProg init, pregenCode, printFutProg trailingCode]
end
