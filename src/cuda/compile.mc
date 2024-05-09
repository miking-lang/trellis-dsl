-- Defines the compilation from the Trellis model AST to CUDA.

include "graph.mc"
include "mexpr/info.mc"

include "../trellis-arg.mc"
include "../constraints/predecessors.mc"
include "../model/ast.mc"
include "../model/encode.mc"
include "../model/merge-subseq-ops.mc"
include "../model/reduce-tables.mc"
include "ast.mc"
include "pprint.mc"

-- Type-related identifiers used in typedefs
let uint8 = nameSym "uint8_t"
let uint16 = nameSym "uint16_t"
let uint32 = nameSym "uint32_t"
let uint64 = nameSym "uint64_t"
let stateTyId = nameSym "state_t"
let obsTyId = nameSym "obs_t"
let probTyId = nameSym "prob_t"

-- Identifiers used in macros
let batchSizeId = nameSym "BATCH_SIZE"
let batchOverlapId = nameSym "BATCH_OVERLAP"
let numStatesId = nameSym "NUM_STATES"
let numObsId = nameSym "NUM_OBS"
let numPredsId = nameSym "NUM_PREDS"
let hmmDeclParamsId = nameSym "HMM_DECL_PARAMS"
let hmmCallArgsId = nameSym "HMM_CALL_ARGS"

-- Identifiers of functions used by the pre-defined parts of the code.
let initProbFunId = nameSym "init_prob"
let outProbFunId = nameSym "output_prob"
let forwProbPredsFunId = nameSym "forward_prob_predecessors"
let viterbiMaxPredsFunId = nameSym "viterbi_max_predecessor"

-- Identifiers used in the predecessor-specific code, reused for simplicity and
-- readability of output code
let stateId = nameSym "state"
let predId = nameSym "pred"
let probId = nameSym "p"

let cinfo = infoVal "Generated by 'src/cuda/compile.mc'" 0 0 0 0

let var = lam id. use TrellisCudaAst in CEVar {id = id}
let uop = lam op. lam arg. use TrellisCudaAst in CEUnOp {op = op, arg = arg}
let bop = lam op. lam l. lam r.
  use TrellisCudaAst in
  CEBinOp {op = op, lhs = l, rhs = r}

lang TrellisCudaCompileBase =
  TrellisModelAst + TrellisCudaAst + TrellisModelPredecessorAnalysis

  type CuCompileEnv = {
    -- Maps the index of each case of the transition probability function to
    -- its representation.
    constraints : [ConstraintRepr],

    -- A sequence of sets representing the indices of constraints that should
    -- be grouped together in the code generation. By grouping constraints
    -- together, we can omit unnecessary if-conditions and compute a more
    -- accurate upper bound on the number of predecessors.
    constraintGroups : [Set Int],

    -- The tables defined in the Trellis model being compiled.
    tables : Map Name TType,

    -- The names of each of the generated transition probability functions,
    -- ordered according to the declaration order of the cases they are
    -- generated from.
    transFunNames : [Name],

    -- Options passed to the compiler.
    opts : TrellisOptions,

    -- Components of the state type.
    stateType : [TType]
  }

  sem cudaTypeDef : CType -> Name -> CuTop
  sem cudaTypeDef ty =
  | id -> {annotations = [], top = CTTyDef {ty = ty, id = id}}

  sem cudaMacroDef : Name -> String -> CuTop
  sem cudaMacroDef id =
  | value -> {annotations = [], top = CTMacroDefine {id = id, value = value}}

  sem cudaIntMacroDef : Name -> Int -> CuTop
  sem cudaIntMacroDef id =
  | value -> cudaMacroDef id (int2string value)

  sem cudaNegInf : () -> CExpr
  sem cudaNegInf =
  | _ ->
    CEBinOp { op = CODiv (), lhs = CEFloat {f = 1.0}, rhs = CEFloat {f = 0.0} }
end

lang TrellisCudaCompileTypeDefs = TrellisCudaCompileBase + TrellisTypeBitwidth
  sem generateTypeDefines : CuCompileEnv -> TModel -> [CuTop]
  sem generateTypeDefines env =
  | model ->
    concat
      (generateIntTypeDefines ())
      (generateModelTypeDefines env model)

  -- NOTE(larshum, 2024-04-26): This generation assumes the hard-coded mapping
  -- from unsigned integer types to sized types is valid, which it should be.
  -- This part is required to avoid having to include headers in the CUDA file
  -- (which is complicated when using nvrtc).
  sem generateIntTypeDefines : () -> [CuTop]
  sem generateIntTypeDefines =
  | _ ->
    let f = lam m.
      match m with (fromType, toTypeId) in
      {annotations = [], top = CTTyDef {ty = fromType, id = toTypeId}}
    in
    map f
    [ (CTyUChar (), uint8),
      (CTyUShort (), uint16),
      (CTyUInt (), uint32),
      (CTyULongLong (), uint64) ]

  sem generateModelTypeDefines : CuCompileEnv -> TModel -> [CuTop]
  sem generateModelTypeDefines env =
  | model ->
    let stateType = chooseMinimalIntegerType model.stateType in
    let obsType = chooseMinimalIntegerType model.outType in
    let probType =
      if env.opts.useDoublePrecisionFloats then CTyDouble ()
      else CTyFloat ()
    in
    [ cudaTypeDef stateType stateTyId
    , cudaTypeDef obsType obsTyId
    , cudaTypeDef probType probTyId ]

  sem chooseMinimalIntegerType : TType -> CType
  sem chooseMinimalIntegerType =
  | trellisTy ->
    let bitwidth = bitwidthType trellisTy in
    if lti bitwidth 8 then CTyVar {id = uint8}
    else if lti bitwidth 16 then CTyVar {id = uint16}
    else if lti bitwidth 32 then CTyVar {id = uint32}
    else if lti bitwidth 64 then CTyVar {id = uint64}
    else
      errorSingle [infoTTy trellisTy] "Bitwise representation of type requires at least 64 bits, which is not supported"
end

lang TrellisCudaConstantDefs = TrellisCudaCompileBase + TrellisTypeCardinality
  sem generateModelConstantDefines : CuCompileEnv -> TModel -> [CuTop]
  sem generateModelConstantDefines env =
  | model ->
    let numStates = cardinalityType model.stateType in
    let numObs = cardinalityType model.outType in
    let numPreds = computeMaxPredecessors env.constraintGroups env.constraints in
    [ cudaIntMacroDef batchSizeId env.opts.batchSize
    , cudaIntMacroDef batchOverlapId env.opts.batchOverlap
    , cudaIntMacroDef numStatesId numStates
    , cudaIntMacroDef numObsId numObs
    , cudaIntMacroDef numPredsId numPreds ]

  sem computeMaxPredecessors : [Set Int] -> [ConstraintRepr] -> Int
  sem computeMaxPredecessors constraintGroups =
  | c ->
    -- NOTE(larshum, 2024-05-09): As the cases (represented by the constraints)
    -- in a group are mutually exclusive in the sense that we run at most one
    -- of the cases, we compute the maximum number of predecessors among all
    -- cases in the group.
    let countMaxPredecessorsInGroup : Set Int -> Int = lam g.
      setFold (lam acc. lam i. maxi acc (countPredecessors (get c i))) 0 g
    in
    foldl addi 0 (map countMaxPredecessorsInGroup constraintGroups)
end

lang TrellisCudaModelMacros = TrellisCudaCompileBase + TrellisCudaPrettyPrint
  sem generateModelMacroDefinitions : CuCompileEnv -> Map Name TExpr -> TModel
                                   -> [CuTop]
  sem generateModelMacroDefinitions env syntheticTables =
  | model ->
    let paramsStr =
      let s = mapFoldWithKey addTableParameter "" model.tables in
      let synTableTypes =
        mapMapWithKey
          (lam id. lam e.
            TTable {args = [], ret = tyTExpr e, info = infoTExpr e})
          syntheticTables
      in
      mapFoldWithKey addTableParameter s synTableTypes
    in
    let argsStr =
      let args =
        map nameGetStr (concat (mapKeys model.tables) (mapKeys syntheticTables))
      in
      strJoin ", " args
    in
    [ cudaMacroDef hmmDeclParamsId paramsStr
    , cudaMacroDef hmmCallArgsId argsStr ]

  -- NOTE(larshum, 2024-04-26): We assume the table takes zero arguments
  -- (scalar) or a single argument (non-scalar) because transformations reduce
  -- multi-argument tables to one-dimensional tables.
  sem compileTrellisTableTypeToCuda : TType -> CType
  sem compileTrellisTableTypeToCuda =
  | TTable {args = [], ret = TProb _} ->
    CTyConst {ty = CTyVar {id = probTyId}}
  | TTable {args = [_], ret = TProb _} ->
    CTyConst {ty = CTyPtr {ty = CTyVar {id = probTyId}}}
  | ty -> error "Compilation of table type not supported"

  sem addTableParameter : String -> Name -> TType -> String
  sem addTableParameter acc tableId =
  | tableType ->
    let ty = compileTrellisTableTypeToCuda tableType in
    match printCType (nameGetStr tableId) pprintEnvEmpty ty with (_, str) in
    if null acc then str
    else join [acc, ", ", str]
end

lang TrellisCudaCompileExpr = TrellisCudaCompileBase + TrellisModelTypePrettyPrint
  sem cudaCompileTrellisExpr : Set Name -> TExpr -> CExpr
  sem cudaCompileTrellisExpr bound =
  | EBool {b = b} -> CEInt {i = if b then 1 else 0}
  | EVar {id = id, info = info} ->
    if setMem id bound then CEVar {id = id}
    else errorSingle [info] "Found unbound variable in CUDA code generation"
  | EInt {i = i} -> CEInt {i = i}
  | EProb {p = p} -> CEFloat {f = log p}
  | ESlice {info = info} ->
    errorSingle [info] "Internal error: Found slice in CUDA code generation"
  | ETableAccess {table = tableId, args = []} ->
    CEVar {id = tableId}
  | ETableAccess {table = tableId, args = [arg]} ->
    CEBinOp {
      op = COSubScript (), lhs = CEVar {id = tableId},
      rhs = cudaCompileTrellisExpr bound arg }
  | ETableAccess {args = [_, _] ++ _, info = info} ->
    errorSingle [info] "Internal error: Expected table access to have zero or one arguments after transformations"
  | EIf {cond = cond, thn = thn, els = els} ->
    CETernary {
      cond = cudaCompileTrellisExpr bound cond,
      thn = cudaCompileTrellisExpr bound thn,
      els = cudaCompileTrellisExpr bound els }
  | EBinOp ({op = OAdd _ | OSub _ | OMul _ | ODiv _ | OMod _} & t) ->
    compileArithmeticOperation bound t
  | EBinOp t ->
    bop (compileOp t.op)
      (cudaCompileTrellisExpr bound t.lhs)
      (cudaCompileTrellisExpr bound t.rhs)

  type BinOpRecord = {op : BOp, lhs : TExpr, rhs : TExpr, ty : TType, info : Info}

  sem compileArithmeticOperation : Set Name -> BinOpRecord -> CExpr
  sem compileArithmeticOperation bound =
  | {op = op, lhs = lhs, rhs = rhs, ty = ty, info = info} ->
    let lhs = cudaCompileTrellisExpr bound lhs in
    let rhs = cudaCompileTrellisExpr bound rhs in
    match ty with TInt _ then
      compileIntegerOperation lhs rhs op
    else match ty with TProb _ then
      compileProbabilityOperation info lhs rhs op
    else
      errorSingle [info]
        (concat "Invalid type of arithmetic operation: " (pprintTrellisType ty))

  sem compileIntegerOperation : CExpr -> CExpr -> BOp -> CExpr
  sem compileIntegerOperation lhs rhs =
  | OAdd _ -> bop (COAdd ()) lhs rhs
  | OSub _ -> bop (COSub ()) lhs rhs
  | OMul _ -> bop (COMul ()) lhs rhs
  | ODiv _ -> bop (CODiv ()) lhs rhs
  | OMod _ -> bop (COMod ()) lhs rhs

  sem compileProbabilityOperation : Info -> CExpr -> CExpr -> BOp -> CExpr
  sem compileProbabilityOperation info lhs rhs =
  | op & (OAdd _ | OSub _) ->
    let cOperator =
      match op with OAdd _ then COAdd () else COSub ()
    in
    -- NOTE(larshum, 2024-05-08): Addition and subtraction on probabilities,
    -- which are represented in a logarithmic scale, requires exponentiating
    -- both arguments and computing the logarithm of the result.
    let expCExpr = lam e. CEApp {fun = nameNoSym "exp", args = [e]} in
    let logCExpr = lam e. CEApp {fun = nameNoSym "log", args = [e]} in
    logCExpr (bop cOperator (expCExpr lhs) (expCExpr rhs))
  | op & (OMul _ | ODiv _) ->
    let cOperator =
      match op with OMul _ then COAdd () else COSub ()
    in
    bop cOperator lhs rhs
  | OMod _ ->
    errorSingle [info] "Modulo operation not supported on probabilities"

  sem compileOp : BOp -> CBinOp
  sem compileOp =
  | OEq _ -> COEq ()
  | ONeq _ -> CONeq ()
  | OLt _ -> COLt ()
  | OGt _ -> COGt ()
  | OLeq _ -> COLe ()
  | OGeq _ -> COGe ()
  | OAnd _ -> COAnd ()
  | OOr _ -> COOr ()
end

lang TrellisCudaCompileSet = TrellisCudaCompileExpr
  sem cudaCompileTrellisSet : TSet -> CExpr
  sem cudaCompileTrellisSet =
  | SAll _ -> CEInt {i = 1}
  | SValueBuilder {x = x, conds = conds} ->
    let joinOr = lam l. lam r. CEBinOp { op = COOr (), lhs = l, rhs = r } in
    let bound = setOfSeq nameCmp [x] in
    let c = map (cudaCompileTrellisExpr bound) conds in
    match c with [h] ++ t then
      foldl joinOr h t
    else CEInt {i = 0}
  | STransitionBuilder {x = x, y = y, conds = conds} ->
    let joinAnd = lam l. lam r. CEBinOp { op = COAnd (), lhs = l, rhs = r} in
    let bound = setOfSeq nameCmp [x, y] in
    let c = map (cudaCompileTrellisExpr bound) conds in
    match c with [h] ++ t then
      foldl joinAnd h t
    else CEInt {i = 1}
end

lang TrellisCudaProbabilityFunction =
  TrellisCudaCompileExpr + TrellisCudaCompileSet

  sem generateProbabilityFunctions : CuCompileEnv -> InitialProbDef
                                  -> OutputProbDef -> TransitionProbDef
                                  -> (CuCompileEnv, [CuTop])
  sem generateProbabilityFunctions env init out =
  | trans ->
    let stateTy = CTyVar {id = stateTyId} in
    let obsTy = CTyVar {id = obsTyId} in
    let initParams = [(stateTy, init.x)] in
    let initFun = generateProbabilityFunction initProbFunId initParams init.cases in
    let outParams = [(stateTy, out.x), (obsTy, out.o)] in
    let outFun = generateProbabilityFunction outProbFunId outParams out.cases in

    -- NOTE(larshum, 2024-04-26): We generate a separate transition probability
    -- function containing the body of each case so we can refer to them
    -- direcly based on our predecessor analysis.
    let transParams = [(stateTy, trans.x), (stateTy, trans.y)] in
    match unzip (map (generateTransitionCaseProbabilityFunction transParams) trans.cases)
    with (funNames, transFuns) in
    let env = {env with transFunNames = funNames} in
    (env, concat [initFun, outFun] transFuns)

  sem generateTransitionCaseProbabilityFunction : [(CType, Name)] -> Case -> (Name, CuTop)
  sem generateTransitionCaseProbabilityFunction params =
  | {cond = _, body = body} ->
    let id = nameSym "transp" in
    let singleCase = {cond = SAll {info = cinfo}, body = body} in
    (id, generateProbabilityFunction id params [singleCase])

  sem generateProbabilityFunction : Name -> [(CType, Name)] -> [Case] -> CuTop
  sem generateProbabilityFunction id params =
  | cases ->
    let bound = setOfSeq nameCmp (map (lam p. p.1) params) in
    let hmmParams = snoc params (CTyEmpty (), hmmDeclParamsId) in
    let body =
      match cases with [{cond = SAll _, body = body}] then
        CSRet {val = Some (cudaCompileTrellisExpr bound body)}
      else
        let baseStmt = CSRet {val = Some (cudaNegInf ())} in
        foldl (generateProbabilityFunctionBody bound) baseStmt cases
    in
    let top = CTFun {
      ret = CTyVar {id = probTyId}, id = id, params = hmmParams, body = [body]
    } in
    {annotations = [CuADevice ()], top = top}

  sem generateProbabilityFunctionBody : Set Name -> CStmt -> Case -> CStmt
  sem generateProbabilityFunctionBody bound acc =
  | {cond = cond, body = body} ->
    CSIf {
      cond = cudaCompileTrellisSet cond,
      thn = [CSRet {val = Some (cudaCompileTrellisExpr bound body)}],
      els = [acc]
    }
end

lang TrellisCudaCompileTransitionCase =
  TrellisCudaCompileExpr + TrellisEncodeExpr + TrellisTypeCardinality +
  TrellisModelMergeSubsequentOperations

  syn CValue =
  -- A fixed component value, constrained by an equality constraint on an
  -- integer literal.
  | CFixed Int

  -- A fixed component value, constrained by an equality constraint on a
  -- component of the to-state, where the integer argument denotes the index of
  -- this component.
  | CFixedY Int

  -- A fixed component value, constrained by a relation to a component of the
  -- to-state. Contains an expression referring to a component of the (encoded)
  -- to-state and a literal offset.
  | CFixedYPlus (TExpr, Int)

  -- A flexible component value, constrained by inequality constraint
  -- specifying particular values the component cannot take.
  | CFlex [Int]

  -- Representation of the values to be generated for a state component.
  type ComponentValue = {
    -- The identifier to which the value of the state component is bound.
    id : Name,

    -- The upper bound value of this component, as determined by its type.
    ub : Int,

    -- A representation of the value of a state component, which is either
    -- fixed to a particular value if it has any equality constraints or
    -- flexible and restricted by zero or more inequality constraints.
    value : CValue
  }

  -- Abstract representation of a case in the transition probability function.
  type TransitionCase = {
    -- A conditional expression determining whether this case is applicable for
    -- a given to-state. This is computed based on the constraints on the
    -- components of the to-state.
    toStateCond : TExpr,

    -- The encoded representation of the predecessor as an integer.
    predecessorExpr : TExpr,

    -- The representation of each component of the from-state, determining the
    -- identifier to which a component is bound and the values it may take.
    predecessorComponents : [ComponentValue],

    -- The name of the transition probability function computing the actual
    -- value to be produced by this case.
    probFunName : Name
  }

  -- Converts the representation of a constraint on a case of the transition
  -- probability function to an abstract representation from which the goal
  -- CUDA code can easily be generated. We use this abstract representation
  -- instead of directly outputting the CUDA code so that we can perform
  -- optimization decisions later, independently of this step.
  sem toTransitionCase : CuCompileEnv -> Name -> ConstraintRepr -> TransitionCase
  sem toTransitionCase env id =
  | repr ->
    let combineTransitionConds = lam exprs.
      joinBoolAnd (map encodeStateOperationsExpr (foldl mergeSubsequentOperations [] exprs))
    in
    let combinePredecessorConds = lam exprs.
      joinAdd 1 (map encodeStateOperationsExpr (foldl mergeSubsequentOperations [] exprs))
    in
    match predecessorCondition env repr with (exprs, components) in
    { toStateCond = combineTransitionConds (transitionCondition env repr)
    , predecessorExpr = combinePredecessorConds exprs
    , predecessorComponents = components
    , probFunName = id }

  -- Combines a sequence of boolean expressions to one expression performing
  -- boolean AND of the components. If the sequence is empty, we return a true
  -- expression.
  sem joinBoolAnd : [TExpr] -> TExpr
  sem joinBoolAnd =
  | [] -> EBool {b = true, ty = TBool {info = cinfo}, info = cinfo}
  | [h] ++ t ->
    let boolAnd = lam acc. lam e.
      EBinOp {
        op = OAnd (), lhs = acc, rhs = e,
        ty = TBool {info = cinfo}, info = cinfo }
    in
    foldl boolAnd h t

  -- Combines a sequence of integer expressions by adding them together.
  sem joinAdd : Int -> [TExpr] -> TExpr
  sem joinAdd n =
  | [] -> error "Internal error: Empty sequence of components"
  | rest ++ [last] ->
    let ty = TInt {bounds = None (), info = cinfo} in
    let expr =
      if eqi n 1 then last
      else
        EBinOp {
          op = OMul (), lhs = last, rhs = EInt {i = n, ty = ty, info = cinfo},
          ty = ty, info = cinfo }
    in
    if null rest then expr
    else
      let n = muli n (cardinalityType (tyTExpr last)) in
      EBinOp {
        op = OAdd (), lhs = joinAdd n rest, rhs = expr,
        ty = ty, info = cinfo }

  -- Given the representation of a set constraint, computes a condition
  -- determining whether a given to-state may have predecessors from this case.
  sem transitionCondition : CuCompileEnv -> ConstraintRepr -> [TExpr]
  sem transitionCondition env =
  | {y = y} ->
    let f = lam acc. lam idx. lam constraints.
      let componentType = get env.stateType idx in
      let componentExpr = lam id. ESlice {
        target = EVar {
          id = id, ty = TTuple {tys = env.stateType, info = cinfo},
          info = cinfo },
        lo = idx, hi = idx, ty = componentType, info = cinfo
      } in
      foldl (addPredConstraint env.stateType stateId componentExpr)
        acc (setToSeq constraints)
    in
    mapFoldWithKey f [] y

  sem addPredConstraint : [TType] -> Name -> (Name -> TExpr) -> [TExpr]
                       -> PredConstraint -> [TExpr]
  sem addPredConstraint stateType componentId componentExpr acc =
  | c ->
    let cexpr = predConstraintToExpr stateType componentId componentExpr c in
    snoc acc cexpr

  sem predConstraintToExpr : [TType] -> Name -> (Name -> TExpr) -> PredConstraint -> TExpr
  sem predConstraintToExpr stateType componentId componentExpr =
  | EqNum (n, _) ->
    let intTy = TInt {bounds = None (), info = cinfo} in
    let arg = EInt { i = n, ty = intTy, info = cinfo } in
    EBinOp { op = OEq (), lhs = componentExpr componentId, rhs = arg,
             ty = TBool {info = cinfo}, info = cinfo }
  | NeqNum (n, _) ->
    let intTy = TInt {bounds = None (), info = cinfo} in
    let arg = EInt { i = n, ty = intTy, info = cinfo } in
    EBinOp { op = ONeq (), lhs = componentExpr componentId, rhs = arg,
             ty = TBool {info = cinfo}, info = cinfo }
  | EqYPlusNum (yidx, n, _) ->
    let intTy = TInt {bounds = None (), info = cinfo} in
    let arg = EBinOp {
      op = OAdd (),
      lhs = componentExpr stateId,
      rhs = EInt { i = n, ty = intTy, info = cinfo },
      ty = intTy, info = cinfo
    } in
    EBinOp { op = OEq (), lhs = componentExpr componentId, rhs = arg,
             ty = TBool {info = cinfo}, info = cinfo }

  -- Given the representation of a set constraint, computes expressions
  -- representing each component of a predecessor. Also, for each component of
  -- the predecessor, computes the values for which it is valid.
  sem predecessorCondition : CuCompileEnv -> ConstraintRepr -> ([TExpr], [ComponentValue])
  sem predecessorCondition env =
  | {state = state, x = x} ->
    let produceComponentRepr = lam i. lam componentSize.
      let value = computeComponentValue env (mapLookup i x) in
      { id = nameSym "x", ub = componentSize, value = value }
    in
    let f = lam c.
      let ty = TInt {bounds = Some (0, subi c.ub 1), info = cinfo} in
      match c.value with CFixed n then
        EInt {i = n, ty = ty, info = cinfo}
      else match c.value with CFixedY yidx then
        let t = EVar {
          id = stateId, ty = TTuple {tys = env.stateType, info = cinfo},
          info = cinfo
        } in
        ESlice {
          target = t, lo = yidx, hi = yidx, ty = get env.stateType yidx,
          info = cinfo }
      else
        EVar {id = c.id, ty = ty, info = cinfo}
    in
    let componentValues = mapi produceComponentRepr state in
    let componentExprs = map f componentValues in
    (map f componentValues, componentValues)

  -- Computes a representation of the value of a component based on the
  -- constraints imposed on it.
  sem computeComponentValue : CuCompileEnv -> Option (Set PredConstraint) -> CValue
  sem computeComponentValue env =
  | None _ -> CFlex []
  | Some constraintsSet ->
    let lookupEqLitConstraint =
      findMap
        (lam c. match c with EqNum (n, _) then Some n else None ())
    in
    let lookupEqYConstraint =
      findMap
        (lam c.
          match c with EqYPlusNum (yidx, n, _) then Some (yidx, n)
          else None ())
    in
    let collectNeqConstraints =
      mapOption (lam c. match c with NeqNum (n, _) then Some n else None ())
    in
    let constraints = setToSeq constraintsSet in
    match lookupEqLitConstraint constraints with Some n then
      CFixed n
    else match lookupEqYConstraint constraints with Some (yidx, n) then
      if eqi n 0 then CFixedY yidx else
      let sliceExpr = ESlice {
        target = EVar {
          id = stateId, ty = TTuple {tys = env.stateType, info = cinfo},
          info = cinfo },
        lo = yidx, hi = yidx, ty = get env.stateType yidx, info = cinfo
      } in
      CFixedYPlus (encodeStateOperationsExpr sliceExpr, n)
    else CFlex (collectNeqConstraints constraints)
end

lang TrellisCudaHMM = TrellisCudaCompileExpr + TrellisCudaCompileTransitionCase

  sem generatePredecessorFunctions : CuCompileEnv -> [CuTop]
  sem generatePredecessorFunctions =
  | env ->
    -- Convert the constraint representation to another intermediate
    -- representation which abstractly represents how we need to compute the
    -- value of each component of a predecessor.
    let transitionCases =
      mapi (lam i. lam c.
        let id = get env.transFunNames i in
        toTransitionCase env id c)
        env.constraints
    in

    -- Group together transition cases based on the result of our earlier
    -- analysis.
    let groups =
      map (lam g. map (get transitionCases) (setToSeq g)) env.constraintGroups
    in

    -- Generate CUDA code for each algorithm, considering each group of cases
    -- one by one.
    [ generateForwardProbPredecessors env groups
    , generateViterbiMaxPredecessors env groups ]

  -- Generates a function used to compute the probability of each predecessor
  -- of a given state. This function is used by the Forward algorithm in the
  -- pre-defined template code.
  sem generateForwardProbPredecessors : CuCompileEnv -> [[TransitionCase]] -> CuTop
  sem generateForwardProbPredecessors env =
  | caseGroups ->
    let alphaPrevId = nameSym "alpha_prev" in
    let instanceId = nameSym "instance" in
    let probsId = nameSym "probs" in
    let params = [
      -- const prob_t *alpha_prev;
      (CTyConst {ty = CTyPtr {ty = CTyVar {id = probTyId}}}, alphaPrevId),
      -- int instance;
      (CTyInt (), instanceId),
      -- state_t state;
      (CTyVar {id = stateTyId}, stateId),
      -- prob_t probs;
      (CTyPtr {ty = CTyVar {id = probTyId}}, probsId),
      -- HMM_DECL_PARAMS
      (CTyEmpty (), hmmDeclParamsId)
    ] in
    let pidx = nameSym "pidx" in
    let forwardCode = CSComp {
      stmts = [
        -- probs[pidx] = p + alpha_prev[instance * NUM_STATES + pred];
        CSExpr { expr =
          bop (COAssign ())
            (bop (COSubScript ()) (var probsId) (var pidx))
            (bop (COAdd ()) (var probId)
              (bop (COSubScript ()) (var alphaPrevId)
                (bop (COAdd ())
                  (bop (COMul ()) (var instanceId) (var numStatesId))
                  (var predId)))) },
        -- pidx = pidx + 1
        CSExpr { expr =
          bop (COAssign ())
            (var pidx)
            (bop (COAdd ()) (var pidx) (CEInt {i = 1})) }
      ]
    } in
    let stmts = map (generatePredecessorsCases env forwardCode) caseGroups in
    let top = CTFun {
      ret = CTyInt (), id = forwProbPredsFunId, params = params,
      body = join [[
        -- int pidx = 0;
        CSDef {
          ty = CTyInt (), id = Some pidx,
          init = Some (CIExpr {expr = CEInt {i = 0}}) },
        -- state_t pred;
        CSDef {
          ty = CTyVar {id = stateTyId}, id = Some predId, init = None () },
        -- prob_t p;
        CSDef {
          ty = CTyVar {id = probTyId}, id = Some probId, init = None () }],
        stmts,
        -- return pidx;
        [CSRet {val = Some (CEVar {id = pidx})}]
      ]
    } in
    { annotations = [CuADevice ()], top = top }

  sem generateViterbiMaxPredecessors : CuCompileEnv -> [[TransitionCase]] -> CuTop
  sem generateViterbiMaxPredecessors env =
  | caseGroups ->
    let chiPrevId = nameSym "chi_prev" in
    let instanceId = nameSym "instance" in
    let maxStateId = nameSym "maxs" in
    let maxProbId = nameSym "maxp" in
    let params = [
      -- const prob_t *chi_prev
      (CTyConst {ty = CTyPtr {ty = CTyVar {id = probTyId}}}, chiPrevId),
      -- int instance;
      (CTyInt (), instanceId),
      -- state_t state;
      (CTyVar {id = stateTyId}, stateId),
      -- state_t *maxs;
      (CTyPtr {ty = CTyVar {id = stateTyId}}, maxStateId),
      -- prob_t *maxp;
      (CTyPtr {ty = CTyVar {id = probTyId}}, maxProbId),
      -- HMM_DECL_PARAMS
      (CTyEmpty (), hmmDeclParamsId)
    ] in
    let viterbiCode = CSComp {
      stmts = [
        -- p = p + chi_prev[instance * NUM_STATES + pred];
        CSExpr {expr =
          bop (COAssign ()) (var probId)
            (bop (COAdd ()) (var probId)
              (bop (COSubScript ()) (var chiPrevId)
                (bop (COAdd ())
                  (bop (COMul ()) (var instanceId) (var numStatesId))
                  (var predId)))) },
        CSIf {
          -- if (p > *maxp) {
          cond = bop (COGt ()) (var probId) (uop (CODeref ()) (var maxProbId)),
          thn = [
            -- *maxs = pred;
            CSExpr {expr =
              bop (COAssign ()) (uop (CODeref ()) (var maxStateId)) (var predId) },
            -- *maxp = p;
            CSExpr {expr =
              bop (COAssign ()) (uop (CODeref ()) (var maxProbId)) (var probId) }
          ],
          els = [] }
      ]
    } in
    let stmts = map (generatePredecessorsCases env viterbiCode) caseGroups in
    let top = CTFun {
      ret = CTyVoid (), id = viterbiMaxPredsFunId, params = params,
      body = concat [
        -- state_t pred;
        CSDef {
          ty = CTyVar {id = stateTyId}, id = Some predId, init = None () },
        -- prob_t p;
        CSDef {
          ty = CTyVar {id = probTyId}, id = Some probId, init = None () }
      ] stmts
    } in
    { annotations = [CuADevice ()], top = top }

  -- Generates a statement computing the predecessors of all provided cases. If
  -- only one case is provided, we insert the tail statement inside the code
  -- generated for that particular state, as the statement may be used multiple
  -- times within a loop. Otherwise, if we have multiple cases, we insert this
  -- tail statement after all cases have ran. This should only happen when the
  -- cases are independent of each other and do not include loops.
  sem generatePredecessorsCases : CuCompileEnv -> CStmt -> [TransitionCase]
                               -> CStmt
  sem generatePredecessorsCases env tailStmt =
  | [c] -> generatePredecessorCase env tailStmt c
  | cases ->
    let nopStmt = CSNop () in
    let stmts = map (generatePredecessorCase env nopStmt) cases in
    CSComp { stmts = snoc stmts tailStmt }

  sem generatePredecessorCase : CuCompileEnv -> CStmt -> TransitionCase -> CStmt
  sem generatePredecessorCase env tailStmt =
  | { toStateCond = toStateCond, predecessorExpr = predecessorExpr
     , predecessorComponents = comps, probFunName = probFunId } ->
    let bound =
      setOfSeq nameCmp (concat [stateId, predId] (map (lam c. c.id) comps))
    in
    let innerStmts = CSComp {stmts = [
      -- pred = <pred expr>;
      CSExpr { expr =
        bop (COAssign ()) (var predId)
          (cudaCompileTrellisExpr bound predecessorExpr)},
      -- p = transp(pred, state, HMM_CALL_ARGS);
      CSExpr { expr =
        bop (COAssign ()) (var probId)
          (CEApp {
            fun = probFunId,
            args = [var predId, var stateId, var hmmCallArgsId]})},
      tailStmt
    ]} in
    let stmt = foldl (generatePredecessorComponent env) innerStmts comps in
    match toStateCond with EBool {b = true} then stmt
    else
      CSIf {
        cond = cudaCompileTrellisExpr bound toStateCond,
        thn = [stmt], els = [] }

  -- Generates code for initializing a particular component, and ensuring that
  -- its value is within its constrained bounds. If a component is only
  -- constrained via inequalities, we generate values in a loop and skip those
  -- that are marked as disallowed.
  sem generatePredecessorComponent : CuCompileEnv -> CStmt -> ComponentValue -> CStmt
  sem generatePredecessorComponent env acc =
  | {value = CFixed _ | CFixedY _} ->
    -- NOTE(larshum, 2024-05-07): For this case, we inline the definition to
    -- allow optimizations, so we do not introduce any new variables here.
    acc
  | {id = id, ub = ub, value = CFixedYPlus (yexpr, n)} ->
    let bound = setOfSeq nameCmp [stateId] in
    let body =
      bop (COAdd ()) (cudaCompileTrellisExpr bound yexpr) (CEInt {i = n})
    in
    let componentDef = CSDef {
      ty = CTyVar {id = stateTyId}, id = Some id,
      init = Some (CIExpr {expr = body})
    } in
    -- NOTE(larshum, 2024-05-09): Following the constraint propagation, we do
    -- not need to do bounds checking for the from-state (predecessor). The
    -- inequality constraints on the to-state will handle this.
    CSComp {stmts = [componentDef, acc]}
  | {id = id, ub = ub, value = CFlex prohibited} ->
    let for = lam id. lam init. lam max. lam body.
      CSComp {stmts = [
        CSDef {
          ty = CTyVar {id = stateTyId}, id = Some id,
          init = Some (CIExpr {expr = CEInt {i = init}}) },
        CSWhile {
          cond = bop (COLt ()) (var id) (CEInt {i = max}),
          body = [
            body,
            CSExpr {expr =
              bop (COAssign ()) (var id) (bop (COAdd ()) (var id) (CEInt {i = 1})) }
          ]}
      ]}
    in
    let body =
      match prohibited with [h] ++ t then
        let neqCheck = lam n. bop (CONeq ()) (var id) (CEInt {i = n}) in
        let combineNeqChecks = lam acc. lam n.
          bop (COAnd ()) acc (neqCheck n)
        in
        let condition = foldl combineNeqChecks (neqCheck h) t in
        CSIf { cond = condition, thn = [acc], els = [] }
      else acc
    in
    for id 0 ub body
end

lang TrellisGroupConstraints = TrellisModelPredecessorAnalysis
  sem groupMutuallyExclusiveConstraints : CuCompileEnv -> CuCompileEnv
  sem groupMutuallyExclusiveConstraints =
  | env ->
    let n = length env.constraints in

    -- Construct an undirected graph where each vertex represents a constraint
    -- representation (a case in the transition probability function). We add
    -- an edge between a pair of cases if they have independent to-states
    -- (meaning at most one of them may run simultaneously for a given
    -- to-state).
    let g =
      foldli
        (lam g. lam i. lam. digraphAddVertexCheck i g true)
        (graphEmpty subi (lam. lam. true)) env.constraints
    in
    let g =
      foldli
        (lam g. lam i. lam c1.
          foldli
            (lam g. lam j. lam c2.
              if gti i j then
                addEdgeIfDisjointToStateConstraints g (i, c1) (j, c2)
              else
                g)
            g env.constraints)
        g env.constraints
    in

    -- Compute the strongly connected components (SCCs) of the undirected graph
    -- using Tarjan's algorithm and attempt to combine these SCCs into distinct
    -- groups.
    -- TODO(larshum, 2024-05-09): Add a more sophisticated analysis that works
    -- better in situations where most cases are pairwise disjoint.
    let sccs = digraphTarjan g in
    {env with constraintGroups = foldl (addDisjointGroups env.constraints) [] sccs}

  -- The property of having disjoint to-states is not transitive. For an SCC
  -- with three or more constraints, we check whether they are all disjoint. If
  -- yes, we group them together, and otherwise we split them up individually
  -- to avoid NP-hard problems.
  sem addDisjointGroups : [ConstraintRepr] -> [Set Int] -> [Int] -> [Set Int]
  sem addDisjointGroups constraints groups =
  | [] ->
    groups
  | ([_] | [_, _]) & s ->
    snoc groups (setOfSeq subi s)
  | scc ->
    let c = map (get constraints) scc in
    let unionY =
      foldl
        (lam acc. lam c.
          {acc with y = mapUnionWith setUnion acc.y c.y,
                    info = mergeInfo acc.info c.info})
        (head c) (tail c)
    in
    switch result.consume (checkEmpty unionY)
    case (_, Right true) then
      snoc groups (setOfSeq subi scc)
    case (_, Right false) then
      concat groups (map (lam i. setOfSeq subi [i]) scc)
    case (_, Left errs) then
      let errStr = printConstraintErrorMessage true (z3Error errs) in
      let msg = join [
        "Grouping of constraints failed:\n", errStr, "\n"
      ] in
      printError msg;
      exit 1
    end

  sem addEdgeIfDisjointToStateConstraints
    : Graph Int () -> (Int, ConstraintRepr) -> (Int, ConstraintRepr) -> Graph Int ()
  sem addEdgeIfDisjointToStateConstraints g x =
  | (j, c2) ->
    match x with (i, c1) in
    switch result.consume (disjointToStateConstraints c1 c2)
    case (_, Right true) then
      graphAddEdge i j () g
    case (_, Right false) then g
    case (_, Left errs) then
      let errStr = printConstraintErrorMessage true (z3Error errs) in
      let msg = join [
        "Grouping of constraints failed:\n", errStr, "\n"
      ] in
      printError msg;
      exit 1
    end
end

lang TrellisCudaCompile =
  TrellisCudaCompileTypeDefs + TrellisCudaConstantDefs + TrellisCudaModelMacros +
  TrellisCudaProbabilityFunction + TrellisCudaHMM + TrellisEncode +
  TrellisModelMergeSubsequentOperations + TrellisGroupConstraints

  sem compileToCuda : TrellisOptions -> Map Name TExpr -> TModel
                   -> Option [ConstraintRepr] -> CuProgram
  sem compileToCuda options syntheticTables model =
  | None _ ->
    error "CUDA code generation does not yet support compilation without a successful predecessor analysis"
  | Some constraints ->
    -- NOTE(larshum, 2024-04-26): We assume the type of the state was declared
    -- as a tuple, or that it has been transformed to one by the compiler.
    let stateTy =
      match model.stateType with TTuple {tys = tys} then tys
      else error "Internal compiler error: state type is not a tuple"
    in

    let env : CuCompileEnv = {
      constraints = constraints, constraintGroups = [], transFunNames = [],
      tables = model.tables, opts = options, stateType = stateTy
    } in

    let env = groupMutuallyExclusiveConstraints env in

    -- Merges operations on subseqent components of the same state or output
    -- among the conditions of a set constraint.
    let model = mergeSubsequentOperationsModel model in

    -- Converts all references to components of a state or output to their
    -- corresponding operations on the encoded integer representation.
    let model = encodeStateOperations env.opts model in

    -- Generate type definitions for sized integer types and the sizes of
    -- integers used to encode states, probabilities, and observations, based
    -- on the model. We define the sized integer types manually to avoid having
    -- to include cstdint, as this is tricky to get right using NVRTC.
    let tyDefs = generateTypeDefines env model in

    -- Generates definitions of constants based on command-line options and
    -- properties of the current model.
    let constDefs = generateModelConstantDefines env model in

    -- Generates macros used to declare and call functions while passing all
    -- tables declared in the model as arguments, to simplify code generation
    -- as all tables are always available where they are needed.
    let modelMacroDefs = generateModelMacroDefinitions env syntheticTables model in

    -- Generates the probability functions based on the model.
    match generateProbabilityFunctions env model.initial model.output model.transition
    with (env, probFunDefs) in

    -- Generates algorithm-specific functions for the Forward and Viterbi
    -- algorithms that make use of our detailed knowledge of predecessors.
    let predFunDefs = generatePredecessorFunctions env in

    {tops = join [tyDefs, constDefs, modelMacroDefs, probFunDefs, predFunDefs]}
end
