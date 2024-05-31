-- Validates the set constraints of a given Trellis model by ensuring that they
-- are non-empty and that they are pairwise disjoint (among the cases of each
-- probability function).
--
-- We want to ensure the set constraints are non-empty as an empty constraint
-- is equivalent to dead code. Most likely, this happens due to a bug in the
-- implementation, so the compiler reports this as an error.
--
-- We ensure set constraints are pairwise disjoint. This is important for the
-- transition probability function because it lets us handle the predecessors
-- more efficiently.

include "../trellis-common.mc"
include "../z3.mc"
include "../constraints/z3.mc"

lang TrellisModelToZ3 = TrellisModelAst + TrellisZ3Ast + TrellisConstraintToZ3
  sem trellisExprToZ3 : Map Name String -> TExpr -> Z3Expr
  sem trellisExprToZ3 nameMap =
  | EBool {b = true} -> ZETrue ()
  | EBool {b = false} -> ZEFalse ()
  | EInt {i = i} -> ZEInt {i = i}
  | EVar {id = id} ->
    match mapLookup id nameMap with Some s then
      ZEVar {id = concat s "0"}
    else error "Unknown variable when converting expression to Z3"
  | ESlice {target = EVar {id = id}, lo = lo, hi = hi} ->
    if eqi lo hi then
      match mapLookup id nameMap with Some s then
        ZEVar {id = concat s (int2string lo)}
      else error "Unknown variable when converting expression to Z3"
    else error "Invalid slice operation when converting expression to Z3"
  | EUnOp {op = op, target = target} ->
    ZEUnOp {op = trellisUnOpToZ3 op, target = trellisExprToZ3 nameMap target}
  | EBinOp {op = op, lhs = lhs, rhs = rhs} ->
    let lhs = trellisExprToZ3 nameMap lhs in
    let rhs = trellisExprToZ3 nameMap rhs in
    ZEBinOp {op = trellisBinOpToZ3 op, lhs = lhs, rhs = rhs}
  | e ->
    errorSingle [infoTExpr e] "Unsupported expression found when converting to Z3"

  sem trellisUnOpToZ3 : UOp -> Z3UOp
  sem trellisUnOpToZ3 =
  | ONot _ -> ZUNot ()

  sem trellisBinOpToZ3 : BOp -> Z3BOp
  sem trellisBinOpToZ3 =
  | OAdd _ -> ZBAdd ()
  | OSub _ -> ZBSub ()
  | OMul _ -> ZBMul ()
  | ODiv _ -> ZBDiv ()
  | OMod _ -> ZBMod ()
  | OEq _ -> ZBEq ()
  | ONeq _ -> ZBNe ()
  | OLt _ -> ZBLt ()
  | OGt _ -> ZBGt ()
  | OLeq _ -> ZBLe ()
  | OGeq _ -> ZBGe ()
  | OAnd _ -> ZBAnd ()
  | OOr _ -> ZBOr ()

  sem trellisSetToZ3 : TSet -> Z3Expr
  sem trellisSetToZ3 =
  | SAll _ -> ZETrue ()
  | SValueBuilder {x = x, conds = conds} ->
    let nameMap = mapFromSeq nameCmp [(x, "x")] in
    foldl1 z3And (map (trellisExprToZ3 nameMap) conds)
  | STransitionBuilder {x = x, y = y, conds = conds} ->
    let nameMap = mapFromSeq nameCmp [(x, "x"), (y, "y")] in
    foldl1 z3And (map (trellisExprToZ3 nameMap) conds)
end

lang TrellisModelValidateBase = TrellisZ3Error
  syn ValidationError =
  | EmptyConstraint Info
  | OverlappingConstraints (Info, Info)
  | Z3RuntimeError String

  sem printValidationErrorMessage : ValidationError -> String
  sem printValidationErrorMessage =
  | EmptyConstraint i ->
    printSection false [i] "Set constraint is empty"
  | OverlappingConstraints (i1, i2) ->
    printSection false [i1, i2] "Set constraints are overlapping"
  | Z3RuntimeError s ->
    concat "Z3 runtime error:\n" s

  sem eqValidationError : ValidationError -> ValidationError -> Bool
  sem eqValidationError lhs =
  | rhs ->
    if eqi (constructorTag lhs) (constructorTag rhs) then
      eqValidationErrorH (lhs, rhs)
    else false

  sem eqValidationErorrH : (ValidationError, ValidationError) -> Bool
  sem eqValidationErrorH =
  | (EmptyConstraint l, EmptyConstraint r) -> eqi (infoCmp l r) 0
  | (OverlappingConstraints (l1, l2), OverlappingConstraints (r1, r2)) ->
    and (eqi (infoCmp l1 r1) 0) (eqi (infoCmp l2 r2) 0)
  | (Z3RuntimeError l, Z3RuntimeError r) -> eqString l r

  sem z3RuntimeError : [Z3Error] -> ValidationError
  sem z3RuntimeError =
  | errs -> Z3RuntimeError (strJoin "\n" (map printZ3Error errs))

  type ValidationResult = Result () ValidationError ()
end

lang TrellisModelValidateNonEmpty =
  TrellisModelValidateBase + TrellisModelToZ3 + TrellisZ3Run

  sem validateNonEmptyCases : ValidationResult -> [Int] -> [Case] -> ValidationResult
  sem validateNonEmptyCases acc stateSizes =
  | cases -> foldl (validateNonEmptyCase stateSizes) acc cases

  sem validateNonEmptyCase : [Int] -> ValidationResult -> Case -> ValidationResult
  sem validateNonEmptyCase stateSizes acc =
  | {cond = cond} ->
    let p = constructSetConstraintNonEmptyProblem stateSizes cond in
    switch result.consume (runZ3SatProgram p)
    case (_, Right true) then acc
    case (_, Right false) then
      result.withAnnotations (result.err (EmptyConstraint (infoTSet cond))) acc
    case (_, Left errs) then
      result.withAnnotations (result.err (z3RuntimeError errs)) acc
    end

  sem constructSetConstraintNonEmptyProblem : [Int] -> TSet -> Z3Program
  sem constructSetConstraintNonEmptyProblem stateSizes =
  | s & (SAll _) -> [ZDAssert {e = ZETrue ()}, ZDCheckSat ()]
  | s & (SValueBuilder {x = x}) ->
    let baseConstraints = z3ImplicitConstraints stateSizes "x" in
    join [baseConstraints, [ZDAssert {e = trellisSetToZ3 s}, ZDCheckSat ()]]
  | s & (STransitionBuilder {x = x, y = y}) ->
    let baseSrcConstraints = z3ImplicitConstraints stateSizes "x" in
    let baseDstConstraints = z3ImplicitConstraints stateSizes "y" in
    join [
      baseSrcConstraints, baseDstConstraints,
      [ZDAssert {e = trellisSetToZ3 s}, ZDCheckSat ()] ]
end

lang TrellisModelValidateDisjoint =
  TrellisModelValidateBase + TrellisModelToZ3 + TrellisZ3Run

  sem validateDisjointCases : ValidationResult -> [Int] -> Bool -> [Case]
                           -> ValidationResult
  sem validateDisjointCases acc stateSizes isTransProb =
  | cases ->
    let checkDisjoint = lam acc. lam lhs. lam rhs.
      let p = constructOverlappingConstraintsProblem stateSizes isTransProb lhs rhs in
      switch result.consume (runZ3SatProgram p)
      case (_, Right false) then acc
      case (_, Right true) then
        let i1 = infoTSet lhs.cond in
        let i2 = infoTSet rhs.cond in
        result.withAnnotations (result.err (OverlappingConstraints (i1, i2))) acc
      case (_, Left errs) then
        result.withAnnotations (result.err (z3RuntimeError errs)) acc
      end
    in
    foldli
      (lam acc. lam idx. lam c1.
        let rhs = subsequence cases (addi idx 1) (length cases) in
        foldl (lam acc. lam c2. checkDisjoint acc c1 c2) acc rhs)
      acc cases

  sem constructOverlappingConstraintsProblem
    : [Int] -> Bool -> Case -> Case -> Z3Program
  sem constructOverlappingConstraintsProblem stateSizes isTransProb l =
  | r ->
    let baseConstraints =
      let base = z3ImplicitConstraints stateSizes "x" in
      if isTransProb then join [base, z3ImplicitConstraints stateSizes "y"]
      else base
    in
    let lhs = trellisSetToZ3 l.cond in
    let rhs = trellisSetToZ3 r.cond in
    join [
      baseConstraints,
      [ ZDAssert {e = ZEBinOp {op = ZBAnd (), lhs = lhs, rhs = rhs}}
      , ZDCheckSat () ] ]
end

lang TrellisModelValidate =
  TrellisModelValidateNonEmpty + TrellisModelValidateDisjoint

  sem validateModelSetConstraints : TModel -> ()
  sem validateModelSetConstraints =
  | {stateType = ty, initial = i, output = o, transition = t} ->
    let stateSizes =
      match ty with TTuple {tys = tys} then map cardinalityType tys
      else [cardinalityType ty]
    in
    let r =
      validateNonEmptyCases (result.ok ()) stateSizes
        (join [i.cases, o.cases, t.cases])
    in
    let r = validateDisjointCases r stateSizes false i.cases in
    let r = validateDisjointCases r stateSizes false o.cases in
    let r = validateDisjointCases r stateSizes true t.cases in
    switch result.consume r
    case (_, Right _) then ()
    case (_, Left errs) then reportValidationError errs
    end

  sem reportValidationError : [ValidationError] -> ()
  sem reportValidationError =
  | errs ->
    let errStrs = strJoin "\n" (map printValidationErrorMessage errs) in
    let msg = join [
      "Model validation failed\n",
      errStrs,
      "\n"
    ] in
    printError msg;
    exit 1
end

mexpr

use TrellisModelValidate in

let i = trellisInfo "trellis-model-validate" in
let caseWithSetConstraint = lam c.
  {cond = c, body = EProb {p = 0.0, ty = TProb {info = i}, info = i}}
in

let isOk = lam l. lam.
  optionIsSome (result.toOption l)
in
let isError = lam l. lam. not (isOk l ()) in

let _bop = lam op. lam lhs. lam rhs.
  EBinOp {op = op, lhs = lhs, rhs = rhs, ty = TBool {info = i}, info = i}
in
let _eq = _bop (OEq ()) in
let _neq = _bop (ONeq ()) in
let _var = lam x. EVar {id = x, ty = TBool {info = i}, info = i} in
let _int = lam n. EInt {i = n, ty = TInt {bounds = None(), info = i}, info = i} in

let x = nameNoSym "x" in
let y = nameNoSym "y" in
let c1 = SAll {info = i} in
let c2 = STransitionBuilder {
  x = x, y = y,
  conds = [_eq (_var x) (_int 0), _neq (_var x) (_int 0)],
  info = i
} in
let c3 = STransitionBuilder {
  x = x, y = y,
  conds = [_eq (_var x) (_int 0)],
  info = i
} in

let cases = map caseWithSetConstraint [c1, c2, c3] in
utest validateNonEmptyCases (result.ok ()) [10] cases with () using isError in
utest validateNonEmptyCases (result.ok ()) [10] [get cases 0] with () using isOk in
utest validateNonEmptyCases (result.ok ()) [10] [get cases 1] with () using isError in
utest validateNonEmptyCases (result.ok ()) [10] [get cases 2] with () using isOk in

()
