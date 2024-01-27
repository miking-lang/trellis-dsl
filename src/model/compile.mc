include "math.mc"
include "seq.mc"
include "futhark/ast.mc"
include "futhark/pprint.mc"

include "ast.mc"
include "bitwise.mc"
include "cardinality.mc"
include "../trellis-arg.mc"

let initialProbabilityId = nameSym "initialProbability"
let outputProbabilityId = nameSym "outputProbability"
let transitionProbabilityId = nameSym "transitionProbability"

let stateTyId = nameSym "state_t"
let probTyId = nameSym "prob_t"
let obsTyId = nameSym "obs_t"
let stateModuleId = nameSym "state"
let probModuleId = nameSym "prob"
let obsModuleId = nameSym "obs"
let nstatesId = nameSym "nstates"

let viterbiId = nameSym "viterbi"

lang TrellisCompileBase = TrellisModelAst + TrellisBitwise + FutharkAst
  -- The environment used throughout compilation of the Trellis model AST.
  type TrellisCompileEnv = {
    -- The command-line options provided by the user
    options : TrellisOptions,

    -- The tables defined in the model
    tables : Map Name FutType,

    -- The declared types of the state and the output
    stateType : TType,
    outputType : TType
  }

  sem probModuleProjection : Info -> String -> FutExpr
  sem probModuleProjection info =
  | id ->
    let probModule =
      FEVar {ident = probModuleId, ty = FTyUnknown {info = info}, info = info}
    in
    FEProj { target = probModule, label = stringToSid id
           , ty = FTyUnknown {info = info}, info = info }

  sem logAppExpr : FutExpr -> FutExpr
  sem logAppExpr =
  | rhs ->
    let info = infoFutTm rhs in
    let logExpr = probModuleProjection info "log" in
    FEApp {lhs = logExpr, rhs = rhs, ty = tyFutTm rhs, info = info}

  sem expAppExpr : FutExpr -> FutExpr
  sem expAppExpr =
  | rhs ->
    let info = infoFutTm rhs in
    let expExpr = probModuleProjection info "exp" in
    FEApp {lhs = expExpr, rhs = rhs, ty = tyFutTm rhs, info = info}

  sem negInfExpr : Info -> FutExpr
  sem negInfExpr =
  | info ->
    FEApp {
      lhs = probModuleProjection info "neg",
      rhs = probModuleProjection info "inf",
      ty = FTyUnknown {info = info}, info = info}
end

lang TrellisCompileInitializer = TrellisCompileBase + FutharkPrettyPrint
  sem chooseIntegerType : Int -> FutType
  sem chooseIntegerType =
  | bits ->
    let sz =
      if leqi bits 8 then U8 ()
      else if leqi bits 16 then U16 ()
      else if leqi bits 32 then U32 ()
      else if leqi bits 64 then U64 ()
      else error "Trellis does not support states requiring more than 63 bits to encode"
    in
    FTyInt {sz = sz, info = NoInfo ()}

  sem validateType : TType -> ()
  sem validateType =
  | TBool _ | TInt {bounds = Some _} -> ()
  | TInt {bounds = None _} | TProb _ | TTable _ ->
    error "Type validation failed: see comment in generateInitializer"
  | TTuple {tys = tys} ->
    iter validateType tys;
    if forAll (lam ty. eqi (slli 1 (bitwidthType ty)) (typeCardinality ty)) tys then
      ()
    else error "Type validation failed: see comment in generateInitializer"

  sem generateInitializer : TrellisCompileEnv -> FutProg
  sem generateInitializer =
  | env ->
    let pprintType = lam ty.
      match pprintType 0 pprintEnvEmpty ty with (_, str) in
      str
    in
    -- TODO(larshum, 2024-01-24): The below validation is meant as a sanity
    -- check, to prevent compilation of programs where the index of each value
    -- and its bitwise representation may differ. I'll get to work on that once
    -- the whole toolchain works.
    validateType env.stateType;
    validateType env.outputType;
    let stateBitwidth = bitwidthType env.stateType in
    let stateTyStr = pprintType (chooseIntegerType stateBitwidth) in
    let outTyStr = pprintType (chooseIntegerType (bitwidthType env.outputType)) in
    let probTy = FTyFloat {
      sz = if env.options.useDoublePrecisionFloats then F64 () else F32 (),
      info = NoInfo ()
    } in
    let probTyStr = pprintType probTy in
    let nstates = slli 1 stateBitwidth in
    FProg {decls = [
      FDeclModuleAlias {ident = stateModuleId, moduleId = stateTyStr, info = NoInfo ()},
      FDeclModuleAlias {ident = obsModuleId, moduleId = outTyStr, info = NoInfo ()},
      FDeclModuleAlias {ident = probModuleId, moduleId = probTyStr, info = NoInfo ()},
      FDeclFun {ident = nstatesId, entry = false, typeParams = [], params = [],
                ret = FTyInt {info = NoInfo (), sz = I64 ()}, body = futInt_ nstates,
                info = NoInfo ()}
    ]}
end

lang TrellisCompileType = TrellisCompileInitializer + TrellisTypeCardinality
  sem compileTrellisType : TrellisCompileEnv -> TType -> FutType
  sem compileTrellisType env =
  | TBool {info = info} -> FTyBool {info = info}
  | ty & (TInt {bounds = Some _, info = info}) ->
    let bitwidth = bitwidthType ty in
    withInfoFutTy info (chooseIntegerType bitwidth)
  | TInt {bounds = None (), info = info} -> FTyInt {sz = I64 (), info = info}
  | TProb {info = info} -> FTyIdent {ident = probTyId, info = info}
  | TTuple {tys = tys, info = info} ->
    errorSingle [info] "Standalone tuple types are not supported"
  | TTable {args = args, ret = ret, info = info} ->
    let buildSizedArrayType = lam dim. lam ty.
      FTyArray {elem = ty, dim = Some (AbsDim dim), info = info}
    in
    let dims = map typeCardinality args in
    let elemTy = compileTrellisType env ret in
    foldr buildSizedArrayType elemTy dims
end

lang TrellisCompileExpr = TrellisCompileBase + TrellisCompileType
  sem compileTrellisExpr : TrellisCompileEnv -> TExpr -> FutExpr
  sem compileTrellisExpr env =
  | EBool {b = b, ty = ty, info = info} ->
    let ty = compileTrellisType env ty in
    FEConst {val = FCBool {val = b}, ty = ty, info = info}
  | EVar {id = id, ty = ty, info = info} ->
    FEVar {ident = id, ty = compileTrellisType env ty, info = info}
  | EInt {i = i, ty = ty, info = info} ->
    let ty = compileTrellisType env ty in
    FEConst {val = FCInt {val = i, sz = None ()}, ty = ty, info = info}
  | EProb {p = p, ty = ty, info = info} ->
    match ty with TProb _ then
      -- NOTE(larshum, 2024-01-24): Here, we convert probability literals to
      -- logscale.
      let ty = compileTrellisType env ty in
      FEConst {val = FCFloat {val = log p, sz = None ()}, ty = ty, info = info}
    else errorSingle [info] "Probability literal was assigned an invalid type"
  | ESlice {target = target, lo = lo, hi = hi, ty = ty, info = info} ->
    errorSingle [info] "Internal error: Found slice when compiling intermediate AST"
  | ETableAccess {table = table, args = args, ty = ty, info = info} ->
    let compileTableArg = lam acc. lam targ.
      let index = compileTrellisExpr env targ in
      FEArrayAccess {
        array = acc, index = convertToI64 index,
        ty = FTyUnknown {info = info}, info = info
      }
    in
    let tableVar = FEVar {ident = table, ty = FTyUnknown {info = info}, info = info} in
    let resultTy = compileTrellisType env ty in 
    withTypeFutTm resultTy (foldl compileTableArg tableVar args)
  | EIf {cond = cond, thn = thn, els = els, ty = ty, info = info} ->
    let cond = compileTrellisExpr env cond in
    let thn = compileTrellisExpr env thn in
    let els = compileTrellisExpr env els in
    let ty = compileTrellisType env ty in
    FEIf {cond = cond, thn = thn, els = els, ty = ty, info = info}
  | EBinOp (t & {op = OAdd _ | OSub _ | OMul _ | ODiv _}) ->
    compileArithmeticOperation env t
  | EBinOp t ->
    let lhs = compileTrellisExpr env t.lhs in
    let rhs = compileTrellisExpr env t.rhs in
    let op = compileTrellisBinOp t.info t.op in
    let opExpr = FEConst {val = op, ty = FTyUnknown {info = t.info}, info = t.info} in
    constructBinOp t.info opExpr lhs rhs

  type BinOpStruct = {op : BOp, lhs : TExpr, rhs : TExpr, ty : TType, info : Info}

  sem constructBinOp : Info -> FutExpr -> FutExpr -> FutExpr -> FutExpr
  sem constructBinOp info op lhs =
  | rhs ->
    let resultTy = tyFutTm lhs in
    let tyuk = FTyUnknown {info = info} in
    FEApp { lhs = FEApp {lhs = op, rhs = lhs, ty = tyuk, info = info}
          , rhs = rhs, ty = resultTy, info = info }

  sem compileTrellisBinOp : Info -> BOp -> FutConst
  sem compileTrellisBinOp info =
  | OAdd _ | OSub _ | OMul _ | ODiv _ ->
    errorSingle [info]
      "Internal error: Arithmetic operations compile differently based on type"
  | OEq _ -> FCEq ()
  | ONeq _ -> FCNeq ()
  | OLt _ -> FCLt ()
  | OGt _ -> FCGt ()
  | OLeq _ -> FCLeq ()
  | OGeq _ -> FCGeq ()
  | OAnd _ -> FCAnd ()
  | OOr _ -> FCOr ()
  | OBitAnd _ -> FCBitAnd ()
  | OSrl _ -> FCSrl ()

  sem compileArithmeticOperation : TrellisCompileEnv -> BinOpStruct -> FutExpr
  sem compileArithmeticOperation env =
  | t ->
    let lhs = compileTrellisExpr env t.lhs in
    let rhs = compileTrellisExpr env t.rhs in
    let ty = compileTrellisType env t.ty in
    match t.ty with TInt _ then
      let c =
        switch t.op
        case OAdd _ then FCAdd ()
        case OSub _ then FCSub ()
        case OMul _ then FCMul ()
        case ODiv _ then FCDiv ()
        end
      in
      let op = FEConst {val = c, ty = ty, info = t.info} in
      constructBinOp t.info op lhs rhs
    else
      -- NOTE(larshum, 2024-01-24): All probability values are represented in
      -- logarithmic scale, so we need to use operations accordingly.
      switch t.op
      case OAdd _ | OSub _ then
        let c = match t.op with OAdd _ then FCAdd () else FCSub () in
        let op = FEConst {val = c, ty = FTyUnknown {info = t.info}, info = t.info} in
        logAppExpr (constructBinOp t.info op (expAppExpr lhs) (expAppExpr rhs))
      case OMul _ | ODiv _ then
        let c = match t.op with OMul _ then FCAdd () else FCSub () in
        let op = FEConst {val = c, ty = ty, info = t.info} in
        constructBinOp t.info op lhs rhs
      end

  sem convertToI64 : FutExpr -> FutExpr
  sem convertToI64 =
  | e ->
    let i = infoFutTm e in
    match tyFutTm e with FTyInt {sz = sz} then
      use FutharkLiteralSizePrettyPrint in
      let intModuleId = nameNoSym (pprintIntSize sz) in
      FEApp {
        lhs = FEProj {
          target = FEVar {ident = intModuleId, ty = FTyUnknown {info = i}, info = i},
          label = stringToSid "to_i64", ty = FTyUnknown {info = i}, info = i},
        rhs = e, ty = FTyInt {sz = I64 (), info = i}, info = i}
    else
      match pprintType 0 pprintEnvEmpty (tyFutTm e) with (_, s) in
      printLn (join ["Expression has type ", s]);
      errorSingle [i] "Table access index was transformed to non-integer type"
end

-- Compiles set expressions to a boolean expression determining whether a given
-- state (or pairs of states) are in the set.
lang TrellisCompileSet = TrellisCompileExpr + TrellisCompileType + TrellisBitwise
  sem binaryOp : FutConst -> FutExpr -> FutExpr -> FutExpr
  sem binaryOp c lhs =
  | rhs ->
    let info = mergeInfo (infoFutTm lhs) (infoFutTm rhs) in
    FEApp {
      lhs = FEApp {
        lhs = FEConst {val = c, ty = FTyUnknown {info = info}, info = info},
        rhs = lhs, ty = FTyUnknown {info = info}, info = info},
      rhs = rhs, ty = FTyUnknown {info = info}, info = info}

  sem boolOr : FutExpr -> FutExpr -> FutExpr
  sem boolOr lhs =
  | rhs -> binaryOp (FCOr ()) lhs rhs

  sem boolAnd : FutExpr -> FutExpr -> FutExpr
  sem boolAnd lhs =
  | rhs -> binaryOp (FCAnd ()) lhs rhs

  sem compileTrellisSet : TrellisCompileEnv -> TSet -> FutExpr
  sem compileTrellisSet env =
  | SAll {info = info} ->
    FEConst {val = FCBool {val = true}, ty = FTyBool {info = info}, info = info}
  | SValueBuilder {conds = conds, info = info}
  | STransitionBuilder {conds = conds, info = info} ->
    let conds = map insertBitwiseOperations conds in
    foldl1 boolAnd (map (compileTrellisExpr env) conds)
  | SValueLiteral {exprs = exprs, info = info} ->
    let exprs = map insertBitwiseOperations exprs in
    foldl1 boolOr (map (compileTrellisExpr env) exprs)
  | STransitionLiteral {exprs = exprs, info = info} ->
    let applyPair = lam f. lam e. (f e.0, f e.1) in
    let exprs = map (applyPair insertBitwiseOperations) exprs in
    let exprs = map (applyPair (compileTrellisExpr env)) exprs in
    foldl1 boolOr (map (lam e. boolAnd e.0 e.1) exprs)
end

lang TrellisCompileProbabilityFunction =
  TrellisCompileExpr + TrellisCompileSet

  type ProbFunRepr = {
    args : [(Name, FutType)],
    decl : FutDecl
  }
  type ProbFuns = (ProbFunRepr, ProbFunRepr, ProbFunRepr)

  sem generateProbabilityFunctions : TrellisCompileEnv -> TModel -> ProbFuns
  sem generateProbabilityFunctions env =
  | model ->
    let stateTy = nFutIdentTy_ stateTyId in
    let outTy = nFutIdentTy_ obsTyId in
    let init = model.initial in
    let initBaseArgs = [(init.x, stateTy)] in
    match generateProbabilityFunction env init.info initialProbabilityId initBaseArgs init.cases
    with (t1, initFun) in
    let out = model.output in
    let outBaseArgs = [(out.x, stateTy), (out.o, outTy)] in
    match generateProbabilityFunction env out.info outputProbabilityId outBaseArgs out.cases
    with (t2, outFun) in
    let trans = model.transition in
    let transBaseArgs = [(trans.x, stateTy), (trans.y, stateTy)] in
    match generateProbabilityFunction env trans.info transitionProbabilityId transBaseArgs trans.cases
    with (t3, transFun) in

    -- If any of the declared tables are unused, we report an error
    -- TODO(larshum, 2024-01-25): Improve this error by using info fields of
    -- the tables, and make it possible to ignore/get a warning.
    let unusedTables = mapDifference env.tables (mapUnion t1 (mapUnion t2 t3)) in
    if mapIsEmpty unusedTables then (initFun, outFun, transFun)
    else
      let unusedTableIds = map nameGetStr (mapKeys unusedTables) in
      error (join ["Model contains unused tables: ", strJoin " " unusedTableIds])

  sem generateProbabilityFunction : TrellisCompileEnv -> Info -> Name -> [(Name, FutType)]
                                 -> [Case] -> (Map Name FutType, ProbFunRepr)
  sem generateProbabilityFunction env info id args =
  | cases ->
    let compileCase = lam c. lam acc.
      let tables = collectUsedTables env.tables acc.0 c.body in
      let cond = compileTrellisSet env c.cond in
      let thn = compileTrellisExpr env (insertBitwiseOperations c.body) in
      ( tables
      , FEIf {
          cond = cond, thn = thn, els = acc.1,
          ty = FTyUnknown {info = info}, info = info} )
    in
    let defaultBody = negInfExpr info in
    match foldr compileCase (mapEmpty nameCmp, defaultBody) cases
    with (tables, body) in
    let args = concat (mapBindings tables) args in
    let funDecl = FDeclFun {
        ident = id, entry = false, typeParams = [],
        params = args, ret = FTyIdent {ident = probTyId, info = info},
        body = body, info = info
    } in
    ( tables, {args = args, decl = funDecl} )

  sem collectUsedTables : Map Name FutType -> Map Name FutType -> TExpr
                       -> Map Name FutType
  sem collectUsedTables tables acc =
  | ETableAccess {table = table} ->
    match mapLookup table tables with Some ty then mapInsert table ty acc
    else acc
  | e -> sfoldTExprTExpr (collectUsedTables tables) acc e
end

lang TrellisCompileModel =
  TrellisCompileInitializer + TrellisCompileProbabilityFunction

  -- The complete output from the compilation of the Trellis model. This
  -- consists of multiple separate pieces that we combine to produce one
  -- Futhark program.
  type TrellisCompileOutput = {
    -- The environment used during compilation
    env : TrellisCompileEnv,

    -- The generated initializer code, which we put at the top of the final
    -- Futhark program.
    initializer : FutProg,

    -- The generated code for the initial, output, and transition
    -- probabilities.
    initial : ProbFunRepr,
    output : ProbFunRepr,
    transition : ProbFunRepr
  }

  sem initCompileEnv : TrellisOptions -> TModel -> TrellisCompileEnv
  sem initCompileEnv options =
  | model ->
    let env =
      { options = options, tables = mapEmpty nameCmp
      , stateType = model.stateType, outputType = model.outType }
    in
    let tables = mapMapWithKey (lam. lam ty. compileTrellisType env ty) model.tables in
    {env with tables = tables}

  sem compileTrellisModel : TrellisOptions -> TModel -> TrellisCompileOutput
  sem compileTrellisModel options =
  | model ->
    let env = initCompileEnv options model in
    match generateProbabilityFunctions env model
    with (initial, output, transition) in
    { env = env, initializer = generateInitializer env, initial = initial
    , output = output, transition = transition }
end
