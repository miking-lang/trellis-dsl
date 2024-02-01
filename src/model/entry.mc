-- Generates the Futhark entry points for the various algorithms to apply to a
-- HMM. We provide multiple entry points to certain algorithms to maximize
-- performance in different situations.

include "mexpr/info.mc"

include "compile.mc"
include "../src-loc.mc"

-- The names of the pre-defined functions in the skeleton code which we glue
-- together with our generated code.
let viterbiHelperId = nameSym "viterbi_helper"
let forwardCpuHelperId = nameSym "forward_helper_cpu"
let forwardGpuHelperId = nameSym "forward_helper_gpu"
let logSumExpId = nameSym "log_sum_exp"

let viterbiEntryId = nameSym "viterbi"
let forwardCpuEntryId = nameSym "forward_cpu"
let forwardGpuEntryId = nameSym "forward_gpu"
let logSumExpEntryId = nameSym "log_sum_exp_entry"

let i = infoVal "trellis-generated" 0 0 0 0

let n = nameSym "n"
let m = nameSym "m"
let predecessorsId = nameSym "predecessors"
let inputsId = nameSym "inputSignals"
let inputLengthsId = nameSym "inputLengths"

lang TrellisGenerateEntry = TrellisCompileModel + FutharkAst
  type FutFunArgs = [(Name, FutType)]

  sem stateI64 : FutExpr -> FutExpr
  sem stateI64 =
  | e ->
    futApp_ (futProj_ (nFutVar_ stateModuleId) "i64") e

  sem generateHigherOrderProbabilityFunctions : FutFunArgs -> FutFunArgs
                                             -> FutFunArgs -> (FutExpr, [Name])
  sem generateHigherOrderProbabilityFunctions initArgs outArgs =
  | transArgs ->
    let initId = nameSym "initp" in
    let outId = nameSym "outp" in
    let transId = nameSym "transp" in
    let probFunIds = [initId, outId, transId] in
    match initArgs with initTableArgs ++ [(x, _)] in
    let initExpr =
      generateHigherOrderProbabilityFunction
        initId initialProbabilityId initTableArgs [x]
    in
    match outArgs with outTableArgs ++ [(x, _), (o, _)] in
    let outExpr =
      generateHigherOrderProbabilityFunction
        outId outputProbabilityId outTableArgs [x, o]
    in
    match transArgs with transTableArgs ++ [(x, _), (y, _)] in
    let transExpr =
      generateHigherOrderProbabilityFunction
        transId transitionProbabilityId transTableArgs [x, y]
    in
    let probFunDeclExpr = futBindall_ [initExpr, outExpr, transExpr] in
    (probFunDeclExpr, probFunIds)

  sem generateHigherOrderProbabilityFunction : Name -> Name -> FutFunArgs -> [Name] -> FutExpr
  sem generateHigherOrderProbabilityFunction id mainDefId tableArgs =
  | mainArgIds ->
    let argIds = concat (map (lam a. a.0) tableArgs) mainArgIds in
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
  sem generateViterbiEntryPoints : TrellisCompileEnv -> FutFunArgs
                                -> FutFunArgs -> FutFunArgs -> [FutDecl]
  sem generateViterbiEntryPoints env initArgs outArgs =
  | transArgs ->
    let params =
      concat
        (mapBindings env.tables)
        [ (predecessorsId, arrayTy stateTyId [None (), Some (NamedDim nstatesId)])
        , (inputsId, arrayTy obsTyId [Some (NamedDim m), Some (NamedDim n)]) ]
    in
    let retTy = arrayTy stateTyId [None (), Some (NamedDim n)] in
    match generateHigherOrderProbabilityFunctions initArgs outArgs transArgs
    with (expr, probFunIds) in
    let body = futBind_ expr (generateViterbiBatchingMap env probFunIds) in
    [FDeclFun {
      ident = viterbiEntryId, entry = true,
      typeParams = [FPSize {val = n}, FPSize {val = m}], params = params,
      ret = retTy, body = body, info = i}]

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
    let baccId = nameSym "bacc" in
    let loopParam = (nFutPvar_ baccId, futVar_ "batchAcc") in
    let idxId = nameSym "i" in
    let viterbiArgs =
      cons
        (nFutVar_ predecessorsId)
        (snoc (map nFutVar_ probFunIds) (futVar_ "batch"))
    in
    let mapFunExpr = nFutLam_ signalId (futBindall_ [
      uFutLet_ "batchAcc" (
        futTabulate_ nbatches (futLam_ "" (
          futTabulate_ bosExpr (futLam_ "" (stateI64 (futInt_ 0)))))),
      uFutLet_ "batchAcc" (
        futForEach_ loopParam idxId (futIndices_ (futVar_ "batchAcc")) (
          futBindall_ [
            uFutLet_ "ofs" (futMul_ (nFutVar_ idxId) bosExpr),
            uFutLet_ "batch" (
              futArraySlice_ (nFutVar_ signalId) (futVar_ "ofs")
                (futAdd_ (futVar_ "ofs") (futInt_ env.options.batchSize))),
            uFutLet_ "out" (
              futAppSeq_ (nFutVar_ viterbiHelperId) viterbiArgs),
            futArrayUpdate_ (nFutVar_ baccId) (nFutVar_ idxId)
              (futArraySlice_ (futVar_ "out") (futInt_ 0) bosExpr)
          ]
        )
      ),
      futSizeCoercion_
        (futFlatten_ (futVar_ "batchAcc"))
        (futSizedArrayTy_ (nFutIdentTy_ stateTyId) outputSize)
    ]) in
    futBindall_ [
      nuFutLet_ nbatchesId nbatchesExpr,
      nuFutLet_ outputSize (futMul_ nbatches bosExpr),
      futMap_ mapFunExpr (nFutVar_ inputsId)
    ]
end

lang TrellisGenerateForwardEntry = TrellisGenerateEntry
  sem generateForwardEntryPoints : TrellisCompileEnv -> FutFunArgs
                                -> FutFunArgs -> FutFunArgs -> [FutDecl]
  sem generateForwardEntryPoints env initArgs outArgs =
  | transArgs ->
    match generateHigherOrderProbabilityFunctions initArgs outArgs transArgs
    with (expr, probFunIds) in
    let gpuTarget =
      match env.options.futharkTarget with "cuda" | "opencl" then true
      else false
    in
    let forwardArgs =
      cons
        (nFutVar_ predecessorsId)
        (map nFutVar_ probFunIds)
    in
    let tables = mapBindings env.tables in
    [ generateForwardEntryCpu tables expr forwardArgs
    , generateForwardEntryGpu tables expr forwardArgs ]

  sem generateForwardEntryCpu : [(Name, FutType)] -> FutExpr -> [FutExpr] -> FutDecl
  sem generateForwardEntryCpu tables probDeclExpr =
  | forwardArgs ->
    let inputLengthsType = FTyArray {
      elem = FTyInt {sz = I64 (), info = i}, dim = Some (NamedDim n), info = i
    } in
    let params =
      concat
        tables
        [ (predecessorsId, arrayTy stateTyId [None (), Some (NamedDim nstatesId)])
        , (inputsId, arrayTy obsTyId [None (), Some (NamedDim n)])
        , (inputLengthsId, inputLengthsType ) ]
    in
    let retTy = arrayTy probTyId [Some (NamedDim n)] in
    let body = futBind_
      probDeclExpr
      (futMap2_
        (futAppSeq_ (nFutVar_ forwardCpuHelperId) forwardArgs)
        (nFutVar_ inputsId)
        (nFutVar_ inputLengthsId))
    in
    FDeclFun {
      ident = forwardCpuEntryId, entry = true,
      typeParams = [FPSize {val = n}], params = params,
      ret = retTy, body = body, info = i}

  sem generateForwardEntryGpu : [(Name, FutType)] -> FutExpr -> [FutExpr] -> FutDecl
  sem generateForwardEntryGpu tables probDeclExpr =
  | forwardArgs ->
    let params =
      concat
        tables
        [ (predecessorsId, arrayTy stateTyId [None (), Some (NamedDim nstatesId)])
        , (inputsId, arrayTy obsTyId [None (), Some (NamedDim n)]) ]
    in
    let retTy = arrayTy probTyId [Some (NamedDim nstatesId), None (), Some (NamedDim n)] in
    let body = futBind_
      probDeclExpr
      (futMap_
        (futAppSeq_ (nFutVar_ forwardGpuHelperId) forwardArgs)
        (nFutVar_ inputsId))
    in
    FDeclFun {
      ident = forwardGpuEntryId, entry = true,
      typeParams = [FPSize {val = n}], params = params,
      ret = retTy, body = body, info = i
    }
end

lang TrellisGenerateLogSumExpEntry = TrellisGenerateEntry
  sem generateLogSumExpEntryPoint : () -> FutDecl
  sem generateLogSumExpEntryPoint =
  | _ ->
    let probs = nameSym "probs" in
    let lens = nameSym "lens" in
    let lensTy = FTyArray {
      elem = FTyInt {sz = I64 (), info = i}, dim = Some (NamedDim n), info = i
    } in
    let params = [
      (probs, arrayTy probTyId [Some (NamedDim nstatesId), None (), Some (NamedDim n)]),
      (lens, lensTy)
    ] in
    let retTy = arrayTy probTyId [Some (NamedDim n)] in
    let body =
      futMap2_
        (futLam_ "p" (futLam_ "len" (
          futApp_
            (nFutVar_ logSumExpId)
            (futArrayAccess_ (futVar_ "p") (futSub_ (futVar_ "len") (futInt_ 1))))))
        (nFutVar_ probs) (nFutVar_ lens)
    in
    FDeclFun {
      ident = logSumExpEntryId, entry = true, typeParams = [FPSize {val = n}],
      params = params, ret = retTy, body = body, info = i
    }
end

lang TrellisGenerateHMMProgram =
  TrellisGenerateViterbiEntry + TrellisGenerateForwardEntry +
  TrellisGenerateLogSumExpEntry + FutharkPrettyPrint

  sem generateHMMProgram : TrellisCompileOutput -> String
  sem generateHMMProgram =
  | {env = env, initializer = init, initial = i, output = o, transition = t} ->
    let viterbi = generateViterbiEntryPoints env i.args o.args t.args in
    let forward = generateForwardEntryPoints env i.args o.args t.args in
    let logSumExp = generateLogSumExpEntryPoint () in
    let pregenCode = readFile (concat trellisSrcLoc "skeleton/hmm.fut") in
    let trailingCode = FProg {
      decls = join [[i.decl, o.decl, t.decl], viterbi, forward, [logSumExp]]
    } in
    strJoin "\n" [printFutProg init, pregenCode, printFutProg trailingCode]
end
