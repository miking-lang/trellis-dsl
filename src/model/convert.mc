-- Defines the conversion from the AST retrieved from parsing the code to a
-- model AST, which is a far simpler AST that only encodes the essential parts
-- of the hidden Markov model without boilerplate from the syn tool.
--
-- We perform a simple type check and type inference for integer bounds as part
-- of this conversion. Specifically, we allow an unbounded integer type (a
-- literal) to be unified with a bounded integer type (a form of subtyping).
-- This ensures that, in the end, all integers have bounds. This enables
-- prevention of out-of-bounds accesses or other sanity checks.

include "utest.mc"

include "ast.mc"
include "eq.mc"
include "pprint.mc"
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

lang TrellisModelConvertExpr =
  TrellisModelConvertType + TrellisModelTypePrettyPrint

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
          if eqi (length args) (length argTypes) then
            match optionMapM checkTTypeH (zip args argTypes) with Some tys then
              let args = map (lam t. withTyTExpr t.0 t.1) (zip tys argExprs) in
              ETableAccess {table = tableId, args = args, ty = ret, info = info}
            else errorSingle [info] "Table argument has wrong type"
          else errorSingle [info] "Wrong number of arguments in table use"
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
    buildOverloadedEqBinOp tyEnv left right info (OEq ())
  | NeqTrellisExpr {left = left, right = right, info = info} ->
    buildOverloadedEqBinOp tyEnv left right info (ONeq ())
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

  sem binOpTypeError : all a. TType -> TType -> Info -> String -> a
  sem binOpTypeError lhs rhs info =
  | msg ->
    errorSingle [info] (join [
      msg, "\n",
      "  LHS: ", pprintTrellisType lhs, "\n",
      "  RHS: ", pprintTrellisType rhs
    ])

  sem buildOverloadedBinOp : Map Name TType -> TrellisExpr -> TrellisExpr -> Info -> BOp -> TExpr
  sem buildOverloadedBinOp tyEnv left right info =
  | op ->
    let lhs = convertTrellisExpr tyEnv left in
    let rhs = convertTrellisExpr tyEnv right in
    let ty =
      let lty = tyTExpr lhs in
      let rty = tyTExpr rhs in
      match (lty, rty) with (TInt _, TInt _) | (TProb _, TProb _) then
        match checkTType lty rty with Some ty then ty
        else binOpTypeError lty rty info "Operator is applied to incompatible arithmetic types"
      else binOpTypeError lty rty info "Operand types mismatch"
    in
    EBinOp {op = op, lhs = lhs, rhs = rhs, ty = ty, info = info}

  sem buildOverloadedEqBinOp : Map Name TType -> TrellisExpr -> TrellisExpr -> Info -> BOp -> TExpr
  sem buildOverloadedEqBinOp tyEnv left right info =
  | op ->
    let lhs = convertTrellisExpr tyEnv left in
    let rhs = convertTrellisExpr tyEnv right in
    let lty = tyTExpr lhs in
    let rty = tyTExpr rhs in
    match checkTType lty rty with Some ty then
      let resTy = TBool {info = info} in
      EBinOp {op = op, lhs = lhs, rhs = rhs, ty = resTy, info = info}
    else binOpTypeError lty rty info "Equality comparison operands have incompatible types"

  sem buildOverloadedCompBinOp : Map Name TType -> TrellisExpr -> TrellisExpr -> Info -> BOp -> TExpr
  sem buildOverloadedCompBinOp tyEnv left right info =
  | op ->
    let lhs = convertTrellisExpr tyEnv left in
    let rhs = convertTrellisExpr tyEnv right in
    let lty = tyTExpr lhs in
    let rty = tyTExpr rhs in
    let ty =
      match (lty, rty) with (TInt _, TInt _) | (TProb _, TProb _) then
        match checkTType lty rty with Some ty then ty
        else binOpTypeError lty rty info "Comparison operands must have compatible arithmetic types"
      else binOpTypeError lty rty info "Comparison operands must have arithmetic types"
    in
    EBinOp {op = op, lhs = lhs, rhs = rhs, ty = ty, info = info}

  sem buildBoolBinOp : Map Name TType -> TrellisExpr -> TrellisExpr -> Info -> BOp -> TExpr
  sem buildBoolBinOp tyEnv left right info =
  | op ->
    let lhs = convertTrellisExpr tyEnv left in
    let rhs = convertTrellisExpr tyEnv right in
    let lty = tyTExpr lhs in
    let rty = tyTExpr rhs in
    match checkTType (tyTExpr lhs) (tyTExpr rhs) with Some (TBool _) then
      EBinOp {op = op, lhs = lhs, rhs = rhs, ty = TBool {info = info}, info = info}
    else binOpTypeError lty rty info "Invalid operand types of boolean operation"
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
    let x = nameNoSym "x" in
    let y = nameNoSym "y" in
    if isTransitionValue (head v) then
      let convertTransition = lam t.
        let to =
          match t.to with Some to then
            convertTrellisExpr tyEnv to
          else
            errorSingle [info] "Literal values must either all be values or transitions"
        in
        let from = convertTrellisExpr tyEnv t.e in
        trellisExprBoolAnd (eqVar info stateType x from) (eqVar info stateType y to)
      in
      let eqExprs = map convertTransition v in
      let conds = foldl1 trellisExprBoolOr eqExprs in
      STransitionBuilder {x = x, y = y, conds = [conds], info = info}
    else
      let convertValue = lam v.
        match v.to with Some _ then
          errorSingle [info] "Literal values must either all be values or transitions"
        else
          eqVar info stateType x (convertTrellisExpr tyEnv v.e)
      in
      let eqExprs = map convertValue v in
      let conds = foldl1 trellisExprBoolOr eqExprs in
      SValueBuilder {x = x, conds = [conds], info = info}

  sem eqVar : Info -> TType -> Name -> TExpr -> TExpr
  sem eqVar info ty x =
  | e ->
    EBinOp {
      op = OEq (), lhs = EVar {id = x, ty = ty, info = info},
      rhs = e, ty = TBool {info = info}, info = info }

  sem trellisExprBoolAnd : TExpr -> TExpr -> TExpr
  sem trellisExprBoolAnd lhs =
  | rhs ->
    let info = mergeInfo (infoTExpr lhs) (infoTExpr rhs) in
    EBinOp {op = OAnd (), lhs = lhs, rhs = rhs, ty = TBool {info = info}, info = info}

  sem trellisExprBoolOr : TExpr -> TExpr -> TExpr
  sem trellisExprBoolOr lhs =
  | rhs ->
    let info = mergeInfo (infoTExpr lhs) (infoTExpr rhs) in
    EBinOp {op = OOr (), lhs = lhs, rhs = rhs, ty = TBool {info = info}, info = info}

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

-- Flattens nested uses of indexing and slicing and tuple types to a flat
-- structure. This makes it easier to reason about the individual components of
-- them. Concretely, after this transformation:
--   1. All tuples of tuples will be converted to a tuple without nesting.
--   2. All indexing operations are translated to work on the flat structure of
--      the target tuple.
lang TrellisModelFlatten = TrellisModelAst
  sem flattenTrellisModelSlices : TModel -> TModel
  sem flattenTrellisModelSlices =
  | {initial = i, output = o, transition = t} & model ->
    let initial = {i with cases = map flattenSlicesCase i.cases} in
    let output = {o with cases = map flattenSlicesCase o.cases} in
    let transition = {t with cases = map flattenSlicesCase t.cases} in
    { model with stateType = flattenType model.stateType,
                 outType = flattenType model.outType,
                 tables = mapMapWithKey (lam. lam v. flattenType v) model.tables,
                 initial = initial, output = output, transition = transition }

  sem flattenSlicesCase : Case -> Case
  sem flattenSlicesCase =
  | c -> {c with body = flattenExpr c.body, cond = flattenSlicesSet c.cond}

  sem flattenSlicesSet : TSet -> TSet
  sem flattenSlicesSet =
  | s -> smapTSetTExpr flattenExpr s

  sem flattenType : TType -> TType
  sem flattenType =
  | TTuple t ->
    let flattenTupleArgTypes = lam tys. lam ty.
      match ty with TTuple t then concat tys t.tys
      else snoc tys ty
    in
    let tys = map flattenType t.tys in
    TTuple {t with tys = foldl flattenTupleArgTypes [] tys}
  | t -> smapTTypeTType flattenType t

  sem flattenExpr : TExpr -> TExpr
  sem flattenExpr =
  | ESlice t ->
    -- Flatten the target expression of the slice, producing the expression and
    -- type of the innermost target and the accumulated offset.
    match flattenSliceExpr (ESlice t) with (target, innerTargetTy, lo, hi) in

    -- If the operation refers to a particular index (a slice with the same
    -- lower and upper bound) and results in a tuple type, we need to make it a
    -- slice operation after flattening.
    match
      if eqi lo hi then
        match t.ty with TTuple {tys = tys} then
          (lo, addi hi (subi (countComponents t.ty) 1))
        else (lo, hi)
      else (lo, hi)
    with (lo, hi) in

    -- Construct the flattened slice operation.
    let target = withTyTExpr innerTargetTy target in
    let sliceTy = sliceType lo hi innerTargetTy in
    ESlice {target = target, lo = lo, hi = hi, ty = sliceTy, info = t.info}
  | e ->
    let e = withTyTExpr (flattenType (tyTExpr e)) e in
    smapTExprTExpr flattenExpr e

  sem flattenSliceExpr : TExpr -> (TExpr, TType, Int, Int)
  sem flattenSliceExpr =
  | ESlice t ->
    match flattenSliceExpr t.target with (target, ty, lo, hi) in
    match tyTExpr t.target with TTuple {tys = tys} then
      match mapAccumL computeComponentOffsets 0 tys with (_, offsets) in
      let target = withTyTExpr t.ty target in
      (target, ty, addi lo (get offsets t.lo), addi hi (get offsets t.hi))
    else errorSingle [t.info] "Invalid type of slice operation"
  | EVar t ->
    let ty = flattenType t.ty in
    (EVar {t with ty = ty}, ty, 0, 0)
  | e -> errorSingle [infoTExpr e] "Invalid slice target"

  sem computeComponentOffsets : Int -> TType -> (Int, Int)
  sem computeComponentOffsets ofs =
  | ty ->
    let c = countComponents ty in
    (addi ofs c, ofs)

  sem countComponents : TType -> Int
  sem countComponents =
  | TTuple t -> foldl (lam acc. lam ty. addi acc (countComponents ty)) 0 t.tys
  | _ -> 1
end

-- Eliminates all uses of slice operations. This assumes slices have been
-- flattened. Concretely, after this pass
--   1. Tuple arguments to tables are passed in a decomposed way, where each
--      component of the tuple is a separate argument.
--   2. Slice operations on tuples are replaced by indexing operations that
--      each produce a non-nested component of a tuple.
lang TrellisModelEliminateSlices = TrellisModelAst
  sem eliminateModelSlices : TModel -> TModel
  sem eliminateModelSlices =
  | {initial = i, output = o, transition = t} & model ->
    let initial = {i with cases = map eliminateSlicesCase i.cases} in
    let output = {o with cases = map eliminateSlicesCase o.cases} in
    let transition = {t with cases = map eliminateSlicesCase t.cases} in
    { model with tables = mapMapWithKey (lam. lam v. eliminateSlicesType v) model.tables,
                 initial = initial, output = output, transition = transition }

  sem eliminateSlicesCase : Case -> Case
  sem eliminateSlicesCase =
  | c -> {c with cond = eliminateSlicesSet c.cond,
                 body = eliminateSlicesExpr c.body}

  sem eliminateSlicesSet : TSet -> TSet
  sem eliminateSlicesSet =
  | SAll t -> SAll t
  | SValueBuilder t ->
    SValueBuilder {t with conds = foldl extractComponentsExpr [] t.conds}
  | STransitionBuilder t ->
    STransitionBuilder {t with conds = foldl extractComponentsExpr [] t.conds}

  sem eliminateSlicesExpr : TExpr -> TExpr
  sem eliminateSlicesExpr =
  | ETableAccess t ->
    ETableAccess {t with args = foldl extractComponentsExpr [] t.args,
                         ty = eliminateSlicesType t.ty}
  | e -> smapTExprTExpr eliminateSlicesExpr e

  sem eliminateSlicesType : TType -> TType
  sem eliminateSlicesType =
  | TTable t -> TTable {t with args = foldl extractComponentsType [] t.args}
  | ty -> smapTTypeTType eliminateSlicesType ty

  sem extractComponentsExpr : [TExpr] -> TExpr -> [TExpr]
  sem extractComponentsExpr acc =
  | ESlice (t & {ty = TTuple {tys = tys}}) ->
    -- NOTE(larshum, 2024-04-09): Convert each slice used as an argument to
    -- multiple arguments, one for each component within it.
    let components = create (length tys) (lam i.
      let idx = addi t.lo i in
      let ty = get tys i in
      ESlice {t with lo = idx, hi = idx, ty = ty}
    ) in
    concat acc components
  | EBinOp (t & {op = op & (OEq _ | ONeq _), lhs = ESlice l, rhs = ESlice r}) ->
    -- NOTE(larshum, 2024-04-09): Convert each equality/inequality on slices to
    -- multiple versions of the same operation on each component the original
    -- slice refers to.
    match (l.ty, r.ty) with (TTuple {tys = ltys}, TTuple {tys = rtys}) then
      if eqi (length ltys) (length rtys) then
        let components = create (length ltys) (lam i.
          let lidx = addi l.lo i in
          let lty = get ltys i in
          let ridx = addi r.lo i in
          let rty = get rtys i in
          EBinOp {t with lhs = ESlice {l with lo = lidx, hi = lidx, ty = lty},
                         rhs = ESlice {r with lo = ridx, hi = ridx, ty = rty}}
        ) in
        concat acc components
      else errorSingle [t.info] "Equality of slices of different lengths"
    else snoc acc (EBinOp t)
  | e -> snoc acc e

  sem extractComponentsType : [TType] -> TType -> [TType]
  sem extractComponentsType acc =
  | (TBool _ | TInt _ | TProb _) & ty -> snoc acc ty
  | TTuple t -> foldl extractComponentsType acc t.tys
  | TTable t -> errorSingle [t.info] "Cannot have nested table types"
end

-- Adjust the integer ranges of all values so that they have a lower bound of
-- zero.
lang TrellisModelAdjustRanges = TrellisModelAst
  sem adjustIntRangesModel : TModel -> TModel
  sem adjustIntRangesModel =
  | {initial = i, output = o, transition = t} & model ->
    let initial = {i with cases = map (adjustIntRangesCase model.tables) i.cases} in
    let output = {o with cases = map (adjustIntRangesCase model.tables) o.cases} in
    let transition = {t with cases = map (adjustIntRangesCase model.tables) t.cases} in
    {model with stateType = adjustIntRangesType model.stateType,
                outType = adjustIntRangesType model.outType,
                tables = mapMapWithKey (lam. lam ty. adjustIntRangesType ty) model.tables,
                initial = initial, output = output, transition = transition}

  sem adjustIntRangesCase : Map Name TType -> Case -> Case
  sem adjustIntRangesCase tableEnv =
  | c ->
    {c with cond = adjustIntRangesSet tableEnv c.cond,
            body = adjustIntRangesExpr tableEnv c.body}

  sem adjustIntRangesSet : Map Name TType -> TSet -> TSet
  sem adjustIntRangesSet tableEnv =
  | s -> smapTSetTExpr (adjustIntRangesExpr tableEnv) s

  sem adjustIntRangesExpr : Map Name TType -> TExpr -> TExpr
  sem adjustIntRangesExpr tableEnv =
  | e & ( EVar {ty = TInt (ti & {bounds = Some (lo, hi)})}
        | ESlice {ty = TInt (ti & {bounds = Some (lo, hi)})}) ->
    if eqi lo 0 then e
    else
      -- NOTE(larshum, 2024-04-09): If the type of a variable is stated to be
      -- non-zero, we adjust its value as the default representation uses lower
      -- bound zero.
      let ofs = EInt {
        i = lo, ty = TInt {bounds = None (), info = infoTExpr e},
        info = infoTExpr e
      } in
      let target =
        match e with EVar t then
          EVar {t with ty = TInt {ti with bounds = Some (0, subi hi lo)}}
        else match e with ESlice t then
          ESlice {t with ty = TInt {ti with bounds = Some (0, subi hi lo)}}
        else never
      in
      EBinOp {
        op = OAdd (), lhs = target,
        rhs = ofs, ty = TInt {ti with bounds = Some (lo, hi)},
        info = infoTExpr e }
  | ETableAccess t ->
    let adjustIntRangesArg = lam arg.
      let arg = adjustIntRangesExpr tableEnv arg in
      match tyTExpr arg with TInt (ti & {bounds = Some (lo, hi)}) then
        -- NOTE(larshum, 2024-04-09): If we access a table using a value of a
        -- type with non-zero lower bound, we adjust it accordingly.
        if neqi lo 0 then
          let ofs = EInt {
            i = lo, ty = TInt {bounds = None (), info = t.info},
            info = t.info
          } in
          EBinOp {
            op = OSub (),
            lhs = arg, rhs = ofs,
            ty = TInt {ti with bounds = Some (0, subi hi lo)}, info = t.info
          }
        else arg
      else arg
    in
    ETableAccess {t with args = map adjustIntRangesArg t.args}
  | e -> smapTExprTExpr (adjustIntRangesExpr tableEnv) e

  sem adjustIntRangesType : TType -> TType
  sem adjustIntRangesType =
  | TInt (t & {bounds = Some (lo, hi)}) ->
    TInt {t with bounds = Some (0, subi hi lo)}
  | ty -> smapTTypeTType adjustIntRangesType ty
end

-- This language fragment defines a function for rewriting the state of the
-- model such that if it has a literal (non-tuple) type, it is rewritten as a
-- singleton tuple.
lang TrellisModelTupleTypes = TrellisModelAst
  sem rewriteModelStateTypeAsTuple : TModel -> TModel
  sem rewriteModelStateTypeAsTuple =
  | model -> rewriteModelStateTypeAsTupleH model model.stateType

  sem rewriteModelStateTypeAsTupleH : TModel -> TType -> TModel
  sem rewriteModelStateTypeAsTupleH model =
  | TTuple _ -> model
  | ty & (TBool _ | TInt _ | TProb _) ->
    {model with stateType = TTuple {tys = [ty], info = infoTTy ty}}
end

lang TrellisModelConvert =
  TrellisModelConvertType + TrellisModelConvertExpr + TrellisModelConvertSet +
  TrellisResolveDeclarations + TrellisModelFlatten +
  TrellisModelEliminateSlices + TrellisModelAdjustRanges +
  TrellisModelTupleTypes

  sem constructTrellisModelRepresentation : TrellisProgram -> TModel
  sem constructTrellisModelRepresentation =
  | p ->
    let inModelDecls = resolveDeclarations p in
    let info = get_TrellisProgram_info p in
    let m = convertToModelRepresentation info inModelDecls in
    let m = flattenTrellisModelSlices m in
    let m = eliminateModelSlices m in
    let m = adjustIntRangesModel m in
    rewriteModelStateTypeAsTuple m

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
    match tyTExpr body with TProb _ then [{cond = allSet, body = body}]
    else errorSingle [infoTExpr body] "Expression must have probability type"
  | CasesProbDecl {cases = cases, info = info} ->
    let boundBody = mapUnion tables args in
    let extractCase = lam acc. lam c.
      let cond = convertTrellisSet tables stateType c.s in
      let body = convertTrellisExpr boundBody c.e in
      match tyTExpr body with TProb _ then snoc acc {cond = cond, body = body}
      else errorSingle [infoTExpr body] "Expression must have probability type"
    in
    foldl extractCase [] cases
end

lang TestLang = TrellisModelConvert + TrellisModelPrettyPrint + TrellisModelEq
end

mexpr

use TestLang in

let trellisEqExpr = eqExpr {defaultTrellisEqOptions () with types = true} in

let printTrellisType = lam l. lam r.
  let pp = lam ty. pprintTrellisType ty in
  utestDefaultToString pp pp l r
in
let printTrellisExpr = lam l. lam r.
  let pp = lam e.
    match pprintTrellisExpr pprintEnvEmpty e with (_, exprStr) in
    let tyStr = pprintTrellisType (tyTExpr e) in
    join [exprStr, " : ", tyStr]
  in
  utestDefaultToString pp pp l r
in

-- Slice flattening tests

-- (x0, (x1, x2), [x3, (x4, x5, x6)], x7, x8)
let i = trellisInfo "trellis-convert" in
let elemTy = TBool {info = i} in
let doublyNestedTupleTy =
  TTuple {info = i, tys = [elemTy, elemTy, elemTy]}
in
let nestedTupleTy = TTuple {info = i, tys = [ elemTy, doublyNestedTupleTy ]} in
let tupleTy = TTuple {
  info = i, tys = [
    elemTy, TTuple {info = i, tys = [elemTy, elemTy]}, nestedTupleTy, elemTy, elemTy
  ]
} in
let flattenedTy = TTuple { tys = create 9 (lam. elemTy), info = i } in
utest flattenType tupleTy with flattenedTy in

let flattenedNestedTy = TTuple {tys = create 4 (lam. elemTy), info = i } in
utest flattenType nestedTupleTy with flattenedNestedTy in

let x = nameNoSym "x" in

-- x[0] -> x[0]
let e = ESlice {
  target = EVar {id = x, ty = tupleTy, info = i},
  lo = 0, hi = 0, ty = elemTy, info = i
} in
let flattened = ESlice {
  target = EVar {id = x, ty = flattenedTy, info = i},
  lo = 0, hi = 0, ty = elemTy, info = i
} in
utest flattenExpr e with flattened using trellisEqExpr else printTrellisExpr in

-- x[2][1][1:2] -> x[5:6]
let e = ESlice {
  target = ESlice {
    target = ESlice {
      target = EVar {id = x, ty = tupleTy, info = i},
      lo = 2, hi = 2, ty = nestedTupleTy, info = i},
    lo = 1, hi = 1, ty = doublyNestedTupleTy, info = i},
  lo = 1, hi = 2, ty = TTuple {tys = [elemTy, elemTy], info = i}, info = i
} in
let flatSliceTy = TTuple { tys = create 2 (lam. elemTy), info = i } in
let flattened = ESlice {
  target = EVar {id = x, ty = flattenedTy, info = i},
  lo = 5, hi = 6, ty = flatSliceTy, info = i
} in
utest flattenExpr e with flattened using trellisEqExpr else printTrellisExpr in

-- x[1] -> x[1:2]
let e = ESlice {
  target = EVar {id = x, ty = tupleTy, info = i},
  lo = 1, hi = 1, ty = TTuple {tys = [elemTy, elemTy], info = i}, info = i
} in
let flattened = ESlice {
  target = EVar {id = x, ty = flattenedTy, info = i},
  lo = 1, hi = 2, ty = TTuple {tys = [elemTy, elemTy], info = i}, info = i
} in
utest flattenExpr e with flattened using trellisEqExpr else printTrellisExpr in

-- x[2] -> x[3:6]
let e = ESlice {
  target = EVar {id = x, ty = tupleTy, info = i},
  lo = 2, hi = 2, ty = nestedTupleTy, info = i
} in
let flattened = ESlice {
  target = EVar {id = x, ty = flattenedTy, info = i},
  lo = 3, hi = 6, ty = TTuple {tys = create 4 (lam. elemTy), info = i}, info = i
} in
utest flattenExpr e with flattened using trellisEqExpr else printTrellisExpr in

-- x[2][1] -> x[4:6]
let e = ESlice {
  target = ESlice {
    target = EVar {id = x, ty = tupleTy, info = i},
    lo = 2, hi = 2, ty = nestedTupleTy, info = i },
  lo = 1, hi = 1, ty = doublyNestedTupleTy, info = i
} in
let flattened = ESlice {
  target = EVar {id = x, ty = flattenedTy, info = i},
  lo = 4, hi = 6, ty = TTuple {tys = create 3 (lam. elemTy), info = i}, info = i
} in
utest flattenExpr e with flattened using trellisEqExpr else printTrellisExpr in

-- x[3:4] -> x[7:8]
let e = ESlice {
  target = EVar {id = x, ty = tupleTy, info = i},
  lo = 3, hi = 4, ty = TTuple {tys = [elemTy, elemTy], info = i}, info = i
} in
let flattened = ESlice {
  target = EVar {id = x, ty = flattenedTy, info = i},
  lo = 7, hi = 8, ty = TTuple {tys = [elemTy, elemTy], info = i}, info = i
} in
utest flattenExpr e with flattened using trellisEqExpr else printTrellisExpr in

-- Slice elimination tests

let slice = lam lo. lam hi.
  let n = addi (subi hi lo) 1 in
  let ty =
    if eqi lo hi then elemTy
    else TTuple {tys = create n (lam. elemTy), info = i}
  in
  ESlice {
    target = EVar {id = x, ty = flattenedTy, info = i},
    lo = lo, hi = hi, ty = ty, info = i}
in

let y = nameNoSym "y" in
let tableAccess = ETableAccess {
  table = y,
  args = [slice 7 8],
  ty = TProb {info = i},
  info = i
} in
let expected = ETableAccess {
  table = y,
  args = [slice 7 7, slice 8 8],
  ty = TProb {info = i},
  info = i
} in
utest eliminateSlicesExpr tableAccess with expected using trellisEqExpr
else printTrellisExpr in

let eqty = TBool {info = i} in
let sliceEq = EBinOp {
  op = OEq (), lhs = slice 2 5, rhs = slice 5 8, ty = eqty, info = i
} in
let expected = [
  EBinOp {op = OEq (), lhs = slice 2 2, rhs = slice 5 5, ty = eqty, info = i},
  EBinOp {op = OEq (), lhs = slice 3 3, rhs = slice 6 6, ty = eqty, info = i},
  EBinOp {op = OEq (), lhs = slice 4 4, rhs = slice 7 7, ty = eqty, info = i},
  EBinOp {op = OEq (), lhs = slice 5 5, rhs = slice 8 8, ty = eqty, info = i}
] in
utest extractComponentsExpr [] sliceEq with expected
using eqSeq trellisEqExpr in

()
