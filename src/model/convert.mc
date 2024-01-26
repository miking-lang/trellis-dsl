-- Defines the conversion from the AST retrieved from parsing the code to a
-- model AST, which is a far simpler AST that only encodes the essential parts
-- of the hidden Markov model without boilerplate from the syn tool.
--
-- We perform a simple type check and type inference for integer bounds as part
-- of this conversion. Specifically, we allow an unbounded integer type (a
-- literal) to be unified with a bounded integer type (a form of subtyping).
-- This ensures that, in the end, all integers have bounds. This enables
-- prevention of out-of-bounds accesses or other sanity checks.

include "ast.mc"
include "../parser/ast.mc"
include "../parser/resolve.mc"

lang TrellisModelConvertType = TrellisModelAst + TrellisAst
  sem convertTrellisType : TrellisType -> TType
  sem convertTrellisType =
  | BoolTrellisType {info = info} -> TBool {info = info}
  | IntTTrellisType {info = info} -> TInt {bounds = None (), info = info}
  | ProbTTrellisType {info = info} -> TProb {info = info}
  | IntRangeTrellisType {lb = {v = lb}, ub = ub, info = info} ->
    match ub with Some {v = ub} then
      TInt {bounds = Some (lb, ub), info = info}
    else errorSingle [info] "Failed to convert upper bound to an integer literal"
  | ArrayTTrellisType {left = left, count = count, info = info} ->
    match count with Some {v = n} then
      let elemTy = convertTrellisType left in
      TTuple {tys = create n (lam. elemTy), info = info}
    else errorSingle [info] "Failed to convert size to an integer literal"
  | TupleTTrellisType {t = t, info = info} ->
    TTuple {tys = map convertTrellisType t, info = info}
end

lang TrellisModelConvertExpr = TrellisModelConvertType
  sem convertTrellisExpr : Map Name TType -> TrellisExpr -> TExpr
  sem convertTrellisExpr tyEnv =
  | TrueTrellisExpr {info = info} ->
    EBool {b = true, ty = TBool {info = info}, info = info}
  | FalseTrellisExpr {info = info} ->
    EBool {b = false, ty = TBool {info = info}, info = info}
  | VarTrellisExpr {id = {v = id}, info = info} ->
    match mapLookup id tyEnv with Some ty then
      EVar {id = id, ty = ty, info = info}
    else errorSingle [info] "Failed to infer type of variable"
  | IntTrellisExpr {i = {v = i}, info = info} ->
    EInt {i = i, ty = TInt {bounds = None (), info = info}, info = info}
  | ProbTrellisExpr {p = {v = p}, info = info} ->
    EProb {p = p, ty = TProb {info = info}, info = info}
  | ProjTrellisExpr {left = left, idx = {v = idx}, info = info} ->
    let target = convertTrellisExpr tyEnv left in
    match tyTExpr target with TTuple {tys = tys} then
      if and (geqi idx 0) (lti idx (length tys)) then
        let resTy = get tys idx in
        ESlice {target = target, lo = idx, hi = idx, ty = resTy, info = info}
      else errorSingle [info] "Projection out of bounds"
    else errorSingle [info] "Projection target has invalid type"
  | TableAccessTrellisExpr {left = left, e = e, info = info} ->
    match convertTrellisExpr tyEnv left with EVar {id = tableId} then
      match mapLookup tableId tyEnv with Some tableTy then
        match tableTy with TTable {args = args, ret = ret} then
          let argExprs = map (convertTrellisExpr tyEnv) e in
          let argTypes = map tyTExpr argExprs in
          match optionMapM checkTTypeH (zip args argTypes) with Some tys then
            let args = map (lam t. withTyTExpr t.0 t.1) (zip tys argExprs) in
            ETableAccess {table = tableId, args = args, ty = ret, info = info}
          else errorSingle [info] "Table argument has wrong type"
        else errorSingle [info] "Table has invalid type"
      else errorSingle [info] "Could not find type of table"
    else errorSingle [info] "Table access must use a valid table name"
  | IfTrellisExpr {c = c, thn = thn, right = right, info = info} ->
    let cond = convertTrellisExpr tyEnv c in
    let thn = convertTrellisExpr tyEnv thn in
    let els = convertTrellisExpr tyEnv right in
    match checkTType (tyTExpr cond) (TBool {info = info}) with Some _ then
      match checkTType (tyTExpr thn) (tyTExpr els) with Some ty then
        let thn = withTyTExpr ty thn in
        let els = withTyTExpr ty els in
        EIf {cond = cond, thn = thn, els = els, ty = ty, info = info}
      else errorSingle [info] "Mismatching types of conditional branches"
    else errorSingle [info] "Condition has non-boolean type"
  | AddTrellisExpr {left = left, right = right, info = info} ->
    buildOverloadedBinOp tyEnv left right info (OAdd ())
  | SubTrellisExpr {left = left, right = right, info = info} ->
    buildOverloadedBinOp tyEnv left right info (OSub ())
  | MulTrellisExpr {left = left, right = right, info = info} ->
    buildOverloadedBinOp tyEnv left right info (OMul ())
  | DivTrellisExpr {left = left, right = right, info = info} ->
    buildOverloadedBinOp tyEnv left right info (ODiv ())
  | EqTrellisExpr {left = left, right = right, info = info} ->
    buildOverloadedCompBinOp tyEnv left right info (OEq ())
  | NeqTrellisExpr {left = left, right = right, info = info} ->
    buildOverloadedCompBinOp tyEnv left right info (ONeq ())
  | LtTrellisExpr {left = left, right = right, info = info} ->
    buildOverloadedCompBinOp tyEnv left right info (OLt ())
  | GtTrellisExpr {left = left, right = right, info = info} ->
    buildOverloadedCompBinOp tyEnv left right info (OGt ())
  | LeqTrellisExpr {left = left, right = right, info = info} ->
    buildOverloadedCompBinOp tyEnv left right info (OLeq ())
  | GeqTrellisExpr {left = left, right = right, info = info} ->
    buildOverloadedCompBinOp tyEnv left right info (OGeq ())
  | AndTrellisExpr {left = left, right = right, info = info} ->
    buildBoolBinOp tyEnv left right info (OAnd ())
  | OrTrellisExpr {left = left, right = right, info = info} ->
    buildBoolBinOp tyEnv left right info (OOr ())

  sem buildOverloadedBinOp : Map Name TType -> TrellisExpr -> TrellisExpr -> Info -> BOp -> TExpr
  sem buildOverloadedBinOp tyEnv left right info =
  | op ->
    let lhs = convertTrellisExpr tyEnv left in
    let rhs = convertTrellisExpr tyEnv right in
    let ty =
      let lty = tyTExpr lhs in
      let rty = tyTExpr rhs in
      match (lty, rty) with (TInt _ | TProb _, TInt _ | TProb _) then
        match checkTType lty rty with Some ty then ty
        else errorSingle [info] "Operator is applied to incompatible arithmetic types"
      else errorSingle [info] "Operand types mismatch"
    in
    EBinOp {op = op, lhs = lhs, rhs = rhs, ty = ty, info = info}

  sem buildOverloadedCompBinOp : Map Name TType -> TrellisExpr -> TrellisExpr -> Info -> BOp -> TExpr
  sem buildOverloadedCompBinOp tyEnv left right info =
  | op ->
    let lhs = convertTrellisExpr tyEnv left in
    let rhs = convertTrellisExpr tyEnv right in
    match checkTType (tyTExpr lhs) (tyTExpr rhs) with Some ty then
      let resTy = TBool {info = info} in
      EBinOp {op = op, lhs = lhs, rhs = rhs, ty = resTy, info = info}
    else errorSingle [info] "Comparison operands have different type"

  sem buildBoolBinOp : Map Name TType -> TrellisExpr -> TrellisExpr -> Info -> BOp -> TExpr
  sem buildBoolBinOp tyEnv left right info =
  | op ->
    let lhs = convertTrellisExpr tyEnv left in
    let rhs = convertTrellisExpr tyEnv right in
    match checkTType (tyTExpr lhs) (tyTExpr rhs) with Some (TBool _) then
      EBinOp {op = op, lhs = lhs, rhs = rhs, ty = TBool {info = info}, info = info}
    else errorSingle [info] "Invalid operand types of boolean operation"
end

lang TrellisModelConvertSet = TrellisModelConvertExpr
  sem convertTrellisSet : Map Name TType -> TType -> TrellisSet -> TSet
  sem convertTrellisSet tyEnv stateType =
  | BuilderTrellisSet {p = p, to = to, e = e, info = info} ->
    let processCondExpr = lam tyEnv. lam bound. lam e.
      let e = substituteBoundPatterns bound (convertTrellisExpr tyEnv e) in
      match tyTExpr e with TBool _ then e
      else
        errorSingle [infoTExpr e] "Condition expression does not have boolean type"
    in
    let x = nameNoSym "x" in
    let xExpr = EVar {id = x, ty = stateType, info = get_TrellisPat_info p} in
    match collectPatternConstraints tyEnv xExpr p with (b1, c1) in
    match to with Some to then
      let y = nameNoSym "y" in
      let yExpr = EVar {id = y, ty = stateType, info = get_TrellisPat_info p} in
      match collectPatternConstraintsH tyEnv yExpr b1 c1 to with (b2, c2) in
      let tyEnv = mapUnion tyEnv (mapMapWithKey (lam. lam e. tyTExpr e) b2) in
      let conds = map (processCondExpr tyEnv b2) e in
      STransitionBuilder {x = x, y = y, conds = concat conds c2, info = info}
    else
      let tyEnv = mapUnion tyEnv (mapMapWithKey (lam. lam e. tyTExpr e) b1) in
      let conds = map (processCondExpr tyEnv b1) e in
      SValueBuilder {x = x, conds = concat conds c1, info = info}
  | LiteralTrellisSet {v = v, info = info} ->
    let isTransitionValue = lam v. match v.to with Some _ then true else false in
    if isTransitionValue (head v) then
      let convertTransition = lam t.
        let to =
          match t.to with Some to then
            convertTrellisExpr tyEnv to
          else
            errorSingle [info] "Literal values must either all be values or transitions"
        in
        (convertTrellisExpr tyEnv t.e, to)
      in
      STransitionLiteral {exprs = map convertTransition v, info = info}
    else
      let convertValue = lam v.
        match v.to with Some _ then
          errorSingle [info] "Literal values must either all be values or transitions"
        else
          convertTrellisExpr tyEnv v.e
      in
      SValueLiteral {exprs = map convertValue v, info = info}

  sem collectPatternConstraints : Map Name TType -> TExpr -> TrellisPat
                              -> (Map Name TExpr, [TExpr])
  sem collectPatternConstraints tyEnv target =
  | p -> collectPatternConstraintsH tyEnv target (mapEmpty nameCmp) [] p

  sem collectPatternConstraintsH : Map Name TType -> TExpr -> Map Name TExpr
                               -> [TExpr] -> TrellisPat -> (Map Name TExpr, [TExpr])
  sem collectPatternConstraintsH tyEnv target binds constraints =
  | VarPTrellisPat {id = {v = id}} ->
    (mapInsert id target binds, constraints)
  | IntPTrellisPat {i = {v = i}, info = info} ->
    match tyTExpr target with TInt {bounds = _} then
      let rhs = EInt {
        i = i, info = info,
        ty = TInt {bounds = None (), info = info}
      } in
      let c = EBinOp {
        op = OEq (), lhs = target, rhs = rhs,
        ty = TBool {info = info}, info = info
      } in
      (binds, snoc constraints c)
    else
      errorSingle [info] "Integer pattern must have integer range type"
  | TruePTrellisPat {info = info} ->
    match tyTExpr target with TBool _ then
      (binds, snoc constraints target)
    else errorSingle [info] "Boolean pattern type mismatch"
  | FalsePTrellisPat {info = info} ->
    let boolExpr = lam b.
      EBool {b = b, ty = TBool {info = info}, info = info}
    in
    match tyTExpr target with TBool _ then
      let c = EIf {
        cond = target, thn = boolExpr false, els = boolExpr true,
        ty = TBool {info = info}, info = info
      } in
      (binds, snoc constraints c)
    else errorSingle [info] "Boolean pattern type mismatch"
  | ArrayPTrellisPat {p = p, info = info} ->
    recursive let partitionArrayPatterns = lam lhs. lam p.
      switch p
      case [] then (lhs, None (), [])
      case [DotsTrellisPat {left = left}] ++ rest then (lhs, Some left, rest)
      case [h] ++ rest then partitionArrayPatterns (snoc lhs h) rest
      end
    in
    let collectConstraintsElement = lam elemTy. lam ofs. lam acc. lam i. lam p.
      match acc with (binds, constraints) in
      let elemTarget = ESlice {
        target = target, lo = i, hi = i, ty = elemTy, info = info
      } in
      collectPatternConstraintsH tyEnv elemTarget binds constraints p
    in
    match tyTExpr target with TTuple {tys = tys} then
      -- NOTE(larshum, 2024-01-24): An empty tuple cannot be constructed
      -- syntactically, so we assume the types are non-empty below.
      match optionMapM (checkTType (head tys)) (tail tys) with Some tys then
        let elemTy = head tys in
        match partitionArrayPatterns [] p with (lhs, dots, rhs) in
        match foldli (collectConstraintsElement elemTy 0) (binds, constraints) lhs
        with (b1, c1) in
        match
          match dots with Some dotsPat then
            match dotsPat with VarPTrellisPat {id = {v = id}} then
              let lo = length lhs in
              let hi = subi (length tys) (length rhs) in
              let dotsLen = subi (length tys) (addi lo (length rhs)) in
              let dotsTy = TTuple {tys = create dotsLen (lam. elemTy), info = info} in
              let dotsTarget = ESlice {
                target = target, lo = lo, hi = hi, ty = dotsTy, info = info
              } in
              (mapInsert id dotsTarget b1, c1)
            else
              errorSingle [info] "The '...' pattern must be attached to a variable"
          else (b1, c1)
        with (b2, c2) in
        let rhsOfs = subi (length tys) (length rhs) in
        foldli (collectConstraintsElement elemTy rhsOfs) (b2, c2) rhs
      else errorSingle [info] "Array pattern type mismatch"
    else errorSingle [info] "Array pattern type mismatch"
  | TuplePTrellisPat {p = p, info = info} ->
    let collectConstraintsElement = lam acc. lam i. lam elem.
      match acc with (binds, constraints) in
      match elem with (p, ty) in
      let info = get_TrellisPat_info p in
      let elemTarget = ESlice {
        target = target, lo = i, hi = i, ty = ty, info = info
      } in
      collectPatternConstraintsH tyEnv elemTarget binds constraints p
    in
    match tyTExpr target with TTuple {tys = tys} then
      foldli collectConstraintsElement (binds, constraints) (zip p tys)
    else errorSingle [info] "Tuple pattern type mismatch"
  | DotsTrellisPat {info = info} ->
    errorSingle [info] "The '...' pattern may only be used in an array pattern"

  sem substituteBoundPatterns : Map Name TExpr -> TExpr -> TExpr
  sem substituteBoundPatterns bound =
  | EVar {id = id, info = info} ->
    match mapLookup id bound with Some e then e
    else errorSingle [info] "Unbound variable in set condition"
  | e -> smapTExprTExpr (substituteBoundPatterns bound) e
end

lang TrellisModelConvert =
  TrellisModelConvertType + TrellisModelConvertExpr + TrellisModelConvertSet +
  TrellisResolveDeclarations

  sem constructTrellisModelRepresentation : TrellisProgram -> TModel
  sem constructTrellisModelRepresentation =
  | p ->
    let inModelDecls = resolveDeclarations p in
    let info = get_TrellisProgram_info p in
    convertToModelRepresentation info inModelDecls

  sem convertToModelRepresentation : Info -> [InModelDecl] -> TModel
  sem convertToModelRepresentation info =
  | modelDecls ->
    let findUnique : all a. (InModelDecl -> Option a) -> (a -> Info) -> String -> a =
      lam f. lam getInfo. lam kind.
      let uniqueF = lam acc. lam decl.
        match acc with Some x then
          match f decl with Some y then
            let infos = [getInfo x, getInfo y] in
            errorSingle infos (concat "Model has multiple definitions of the " kind)
          else Some x
        else f decl
      in
      match foldl uniqueF (None ()) modelDecls with Some x then x
      else errorSingle [info] (concat "Model does not define the " kind)
    in
    let stateType = findUnique extractStateType infoTTy "type of a state" in
    let outputType = findUnique extractOutputType infoTTy "type of an output" in
    let tables = extractTables modelDecls in
    let initial =
      findUnique (extractInitialProbDef tables stateType) (lam x. x.info)
                 "initial probability function"
    in
    let output =
      findUnique (extractOutputProbDef tables stateType outputType) (lam x. x.info)
                 "output probability function"
    in
    let transition =
      findUnique (extractTransitionProbDef tables stateType) (lam x. x.info)
                 "transition probability function"
    in
    { stateType = stateType, outType = outputType, tables = tables
    , initial = initial, output = output, transition = transition }

  sem extractTables : [InModelDecl] -> Map Name TType
  sem extractTables =
  | modelDecls -> foldl extractTablesH (mapEmpty nameCmp) modelDecls

  sem extractTablesH : Map Name TType -> InModelDecl -> Map Name TType
  sem extractTablesH tables =
  | TableInModelDecl {id = {v = id}, dim = dim, ty = ty, info = info} ->
    let args = map convertTrellisType dim in
    let ret = convertTrellisType ty in
    let tableTy = TTable {args = args, ret = ret, info = info} in
    mapInsert id tableTy tables
  | _ -> tables

  sem extractStateType : InModelDecl -> Option TType
  sem extractStateType =
  | StatePropertyInModelDecl {ty = ty} -> Some (convertTrellisType ty)
  | _ -> None ()

  sem extractOutputType : InModelDecl -> Option TType
  sem extractOutputType =
  | OutputPropertyInModelDecl {ty = ty} -> Some (convertTrellisType ty)
  | _ -> None ()

  sem extractInitialProbDef : Map Name TType -> TType -> InModelDecl -> Option InitialProbDef
  sem extractInitialProbDef tables stateType =
  | ProbInModelDecl {init = Some _, fst = {v = x}, pd = pd, info = info} ->
    let args = mapFromSeq nameCmp [(x, stateType)] in
    Some {x = x, cases = extractProbDecl tables args stateType pd, info = info}
  | _ -> None ()

  sem extractOutputProbDef : Map Name TType -> TType -> TType -> InModelDecl -> Option OutputProbDef
  sem extractOutputProbDef tables stateType outputType =
  | ProbInModelDecl {out = Some _, fst = {v = o}, snd = Some {v = x}, pd = pd, info = info} ->
    let args = mapFromSeq nameCmp [(x, stateType), (o, outputType)] in
    Some {x = x, o = o, cases = extractProbDecl tables args stateType pd, info = info}
  | _ -> None ()

  sem extractTransitionProbDef : Map Name TType -> TType -> InModelDecl -> Option TransitionProbDef
  sem extractTransitionProbDef tables stateType =
  | ProbInModelDecl {trans = Some _, fst = {v = x}, snd = Some {v = y}, pd = pd, info = info} ->
    let args = mapFromSeq nameCmp [(x, stateType), (y, stateType)] in
    Some {x = x, y = y, cases = extractProbDecl tables args stateType pd, info = info}
  | _ -> None ()

  sem extractProbDecl : Map Name TType -> Map Name TType -> TType -> ProbDecl -> [Case]
  sem extractProbDecl tables args stateType =
  | OneProbDecl {e = e, info = info} ->
    let allSet = SAll {info = info} in
    let boundBody = mapUnion tables args in
    let body = convertTrellisExpr boundBody e in
    [{cond = allSet, body = body}]
  | CasesProbDecl {cases = cases, info = info} ->
    let boundBody = mapUnion tables args in
    let extractCase = lam acc. lam c.
      let cond = convertTrellisSet tables stateType c.s in
      let body = convertTrellisExpr boundBody c.e in
      snoc acc {cond = cond, body = body}
    in
    foldl extractCase [] cases
end
