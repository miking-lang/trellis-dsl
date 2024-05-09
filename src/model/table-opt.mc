-- This file defines an analysis which replaces non-trivial expressions in the
-- body of a case in a probability function with a direct reference to a
-- synthetic table which is assumed to contain the pre-computed value of the
-- expression. The analysis applies to any compound (non-trivial) expressions
-- which may involve both literals and references to other tables of the model.
-- Importantly, the expression must be independent of the arguments passed to
-- the probability function (states and observations).
--
-- This analysis enables us to optimize the performance by replacing the
-- evaluation of a potentially non-trivial expression with a pre-computed
-- value in the body of a case in a probability function.
include "map.mc"
include "name.mc"
include "set.mc"

include "ast.mc"

lang TrellisModelReplaceNonTrivialBody = TrellisModelAst
  -- Replaces the bodies of cases in the probability functions as described
  -- at the top of the file. The result is the updated model, potentially
  -- containing new synthetic tables, and a mapping from the identifiers of
  -- these synthetic tables to the expressions they represent.
  sem replaceNonTrivialBodiesInProbabilityFunctions : TModel -> (Map Name TExpr, TModel)
  sem replaceNonTrivialBodiesInProbabilityFunctions =
  | model ->
    let initVars = setOfSeq nameCmp [model.initial.x] in
    match mapAccumL (replaceNonTrivialBodyCase initVars) (mapEmpty nameCmp) model.initial.cases
    with (env, initCases) in
    let outVars = setOfSeq nameCmp [model.output.x, model.output.o] in
    match mapAccumL (replaceNonTrivialBodyCase outVars) env model.output.cases
    with (env, outCases) in
    let transVars = setOfSeq nameCmp [model.transition.x, model.transition.y] in
    match mapAccumL (replaceNonTrivialBodyCase transVars) env model.transition.cases
    with (env, transCases) in
    let model =
      {model with initial = {model.initial with cases = initCases},
                  output = {model.output with cases = outCases},
                  transition = {model.transition with cases = transCases}}
    in
    (env, model)

  sem replaceNonTrivialBodyCase : Set Name -> Map Name TExpr -> Case -> (Map Name TExpr, Case)
  sem replaceNonTrivialBodyCase boundVars acc =
  | c ->
    if isEligibleForReplacement boundVars c.body then
      let syntheticTableId =
        let id = nameSym "synthetic" in
        let sym =
          match nameGetSym id with Some s then sym2hash s
          else error "impossible"
        in
        nameNoSym (join [nameGetStr id, "_", int2string sym])
      in
      let info = infoTExpr c.body in
      let body = ETableAccess {
        table = syntheticTableId, args = [],
        ty = TTable {args = [], ret = tyTExpr c.body, info = info}, info = info
      } in
      (mapInsert syntheticTableId c.body acc, {c with body = body})
    else (acc, c)

  -- Determines whether a given expression is considered eligible for being
  -- replaced with a reference to a pre-computed value. We do not replace
  -- trivial expressions (including direct references to an existing table),
  -- and we only consider compound expressions which have no references to the
  -- variables passed to the probability functions. In this case, they are
  -- constant and can be replaced with a fixed pre-computed value.
  sem isEligibleForReplacement : Set Name -> TExpr -> Bool
  sem isEligibleForReplacement boundVars =
  | EBool _ | EVar _ | EInt _ | EProb _ | ETableAccess _ -> false
  | e -> not (dependsOnBoundVariables boundVars e)

  -- Determines whether a given expression directly depends on the given set of
  -- bound variables.
  sem dependsOnBoundVariables : Set Name -> TExpr -> Bool
  sem dependsOnBoundVariables boundVars =
  | EBool _ | EInt _ | EProb _ -> false
  | EVar t -> if setMem t.id boundVars then true else false
  | ESlice t -> dependsOnBoundVariables boundVars t.target
  | ETableAccess t ->
    match t.args with [] then false
    else match t.args with [a] then dependsOnBoundVariables boundVars a
    else errorSingle [t.info] "Internal error: Found multi-dimensional table"
  | EIf t -> any (dependsOnBoundVariables boundVars) [t.cond, t.thn, t.els]
  | EBinOp t ->
    let f = dependsOnBoundVariables boundVars in
    or (f t.lhs) (f t.rhs)
end

mexpr

use TrellisModelReplaceNonTrivialBody in

let x = nameSym "x" in
let y = nameSym "y" in
let z = nameSym "z" in
let b1 = setEmpty nameCmp in
let b2 = setOfSeq nameCmp [x, y] in
let b3 = setOfSeq nameCmp [y, z] in
let b4 = setOfSeq nameCmp [x, y, z] in

let ty = TBool {info = NoInfo ()} in
let var = lam id. EVar {id = id, ty = ty, info = NoInfo ()} in
let e1 = var x in
utest dependsOnBoundVariables b1 e1 with false in
utest dependsOnBoundVariables b2 e1 with true in
utest dependsOnBoundVariables b3 e1 with false in
utest dependsOnBoundVariables b4 e1 with true in

let e2 = EBinOp {
  op = OAdd (), lhs = var y, rhs = EInt {i = 1, ty = ty, info = NoInfo ()},
  ty = ty, info = NoInfo ()
} in
utest dependsOnBoundVariables b1 e2 with false in
utest dependsOnBoundVariables b2 e2 with true in
utest dependsOnBoundVariables b3 e2 with true in
utest dependsOnBoundVariables b4 e2 with true in

let e3 = ETableAccess {
  table = nameNoSym "t", args = [var z], ty = ty, info = NoInfo ()
} in
utest dependsOnBoundVariables b1 e3 with false in
utest dependsOnBoundVariables b2 e3 with false in
utest dependsOnBoundVariables b3 e3 with true in
utest dependsOnBoundVariables b4 e3 with true in

let bool = lam b. EBool {b = b, ty = ty, info = NoInfo ()} in
let e4 = EIf {
  cond = bool true, thn = bool false, els = bool true, ty = ty, info = NoInfo ()
} in
utest dependsOnBoundVariables b1 e4 with false in
utest dependsOnBoundVariables b2 e4 with false in
utest dependsOnBoundVariables b3 e4 with false in
utest dependsOnBoundVariables b4 e4 with false in


()
