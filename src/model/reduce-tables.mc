-- Reduces the dimensionality of all tables defined in the Trellis model to
-- one. We do this by treating table argument types as a single type with a
-- larger integer range.

include "ast.mc"
include "encode.mc"
include "eq.mc"
include "pprint.mc"

lang TrellisReduceTableDimensionality = TrellisModelAst + TrellisTypeCardinality
  sem reduceTableDimensionalityModel : TModel -> TModel
  sem reduceTableDimensionalityModel =
  | {initial = i, output = o, transition = t} & model ->
    let tables = mapMapWithKey (lam. lam ty. reduceTableDimensionalityType ty) model.tables in
    let initial = {i with cases = map reduceTableDimensionalityCase i.cases} in
    let output = {o with cases = map reduceTableDimensionalityCase o.cases} in
    let transition = {t with cases = map reduceTableDimensionalityCase t.cases} in
    { model with tables = tables, initial = initial, output = output,
                 transition = transition }

  sem reduceTableDimensionalityCase : Case -> Case
  sem reduceTableDimensionalityCase =
  | c ->
    {c with cond = reduceTableDimensionalitySet c.cond,
            body = reduceTableDimensionalityExpr c.body}

  sem reduceTableDimensionalitySet : TSet -> TSet
  sem reduceTableDimensionalitySet =
  | s -> smapTSetTExpr reduceTableDimensionalityExpr s

  sem reduceTableDimensionalityType : TType -> TType
  sem reduceTableDimensionalityType =
  | TTable t ->
    if null t.args then TTable t
    else
      let cards = map cardinalityType t.args in
      let totCardinality = foldl muli 1 cards in
      let argType = TInt {
        bounds = Some (0, subi totCardinality 1), info = t.info
      } in
      TTable {t with args = [argType]}
  | ty -> smapTTypeTType reduceTableDimensionalityType ty

  sem reduceTableDimensionalityExpr : TExpr -> TExpr
  sem reduceTableDimensionalityExpr =
  | ETableAccess t ->
    let args = foldl mergeSubsequentSlices [] t.args in
    let cards = map (lam e. cardinalityType (tyTExpr e)) args in
    let ub = foldl muli 1 cards in
    let toMixedRadixIndex = lam i. lam arg.
      let fst = addi i 1 in
      let n = subi (length args) fst in
      let multiplier = foldl muli 1 (subsequence cards fst n) in
      match multiplier with 1 then arg
      else
        EBinOp {
          op = OMul (), lhs = arg,
          rhs = EInt {
            i = multiplier, ty = TInt {bounds = None (), info = t.info},
            info = t.info},
          ty = TInt {bounds = None (), info = t.info}, info = t.info }
    in
    let exprs = mapi toMixedRadixIndex args in
    let addExprs = lam l. lam r.
      EBinOp {
        op = OAdd (), lhs = l, rhs = r,
        ty = TInt {bounds = Some (0, subi ub 1), info = t.info}, info = t.info }
    in
    let indexExpr =
      match exprs with [] then []
      else match exprs with [h] ++ t then [foldl addExprs h t]
      else never
    in
    ETableAccess {t with args = indexExpr}
  | e -> smapTExprTExpr reduceTableDimensionalityExpr e

  sem mergeSubsequentSlices : [TExpr] -> TExpr -> [TExpr]
  sem mergeSubsequentSlices acc =
  | e & (ESlice (t & {target = EVar {id = tid}})) ->
    match acc with a ++ [ESlice {target = EVar {id = id}, lo = l, hi = h, ty = ty}] then
      if nameEq tid id then
        if and (leqi (addi l 1) t.lo) (eqi (addi h 1) t.hi) then
          let sliceTy =
            match t.ty with TTuple tt then
              TTuple {tt with tys = snoc tt.tys ty}
            else
              TTuple {tys = [t.ty, ty], info = t.info}
          in
          snoc a (ESlice {t with lo = l, ty = sliceTy})
        else snoc acc e
      else snoc acc e
    else snoc acc e
  | e -> snoc acc e
end

lang TestLang =
  TrellisReduceTableDimensionality + TrellisModelEq + TrellisModelPrettyPrint
end

mexpr

use TestLang in

let ppExprs = lam l. lam r.
  let pp = lam e.
    match pprintTrellisExpr pprintEnvEmpty e with (_, s) in
    s
  in
  utestDefaultToString pp pp l r
in
-- NOTE(larshum, 2024-04-09): We ignore the types because they are irrelevant
-- at this stage in the compilation.
let eqExpr = eqExpr {defaultTrellisEqOptions () with types = false} in

let i = trellisInfo "trellis-reduce-tables" in
let tyint = lam lo. lam hi. TInt {bounds = Some (lo, hi), info = i} in

-- t : (0..4, 0..5, 0..6) -> Probability
-- t(x, y, z) <==> t(42x+7y+z)
let e = ETableAccess {
  table = nameNoSym "t",
  args = [
    EVar {id = nameNoSym "x", ty = tyint 0 4, info = i},
    EVar {id = nameNoSym "y", ty = tyint 0 5, info = i},
    EVar {id = nameNoSym "z", ty = tyint 0 6, info = i}
  ],
  ty = TProb {info = i}, info = i
} in
let expected = ETableAccess {
  table = nameNoSym "t",
  args = [
    EBinOp {
      op = OAdd (),
      lhs = EBinOp {
        op = OAdd (),
        lhs = EBinOp {
          op = OMul (),
          lhs = EVar {id = nameNoSym "x", ty = tyint 0 4, info = i},
          rhs = EInt {i = 42, ty = tyint 0 210, info = i},
          ty = tyint 0 210, info = i},
        rhs = EBinOp {
          op = OMul (),
          lhs = EVar {id = nameNoSym "y", ty = tyint 0 5, info = i},
          rhs = EInt {i = 7, ty = tyint 0 210, info = i},
          ty = tyint 0 210, info = i},
        ty = tyint 0 210, info = i},
      rhs = EVar {id = nameNoSym "z", ty = tyint 0 6, info = i},
      ty = tyint 0 210, info = i}
  ],
  ty = TProb {info = i}, info = i
} in
utest reduceTableDimensionalityExpr e with expected using eqExpr else ppExprs in

-- x : (0..3, 0..3, 0..3, 1..16)
-- t(x[0], x[1], x[2]) <==> t(x[0:2])
let x = EVar {
  id = nameNoSym "x",
  ty = TTuple {tys = [tyint 0 3, tyint 0 3, tyint 0 3, tyint 1 16], info = i},
  info = i
} in
let e = ETableAccess {
  table = nameNoSym "t",
  args = [
    ESlice {target = x, lo = 0, hi = 0, ty = tyint 0 3, info = i},
    ESlice {target = x, lo = 1, hi = 1, ty = tyint 0 3, info = i},
    ESlice {target = x, lo = 2, hi = 2, ty = tyint 0 3, info = i}
  ],
  ty = TProb {info = i}, info = i
} in
let expected = ETableAccess {
  table = nameNoSym "t",
  args = [
    ESlice {target = x, lo = 0, hi = 2, ty = tyint 0 64, info = i}
  ],
  ty = TProb {info = i}, info = i
} in
utest reduceTableDimensionalityExpr e with expected using eqExpr else ppExprs in

-- x, y : (0..3, 0..3, 0..3, 1..16)
-- t(x[0], x[1], y[2]) <==> t(x[0:1] * 4 + y[2])
let y = EVar {
  id = nameNoSym "y",
  ty = TTuple {tys = [tyint 0 3, tyint 0 3, tyint 0 3, tyint 1 16], info = i},
  info = i
} in
let e = ETableAccess {
  table = nameNoSym "t",
  args = [
    ESlice {target = x, lo = 0, hi = 0, ty = tyint 0 3, info = i},
    ESlice {target = x, lo = 1, hi = 1, ty = tyint 0 3, info = i},
    ESlice {target = y, lo = 2, hi = 2, ty = tyint 0 3, info = i}
  ],
  ty = TProb {info = i}, info = i
} in
let expected = ETableAccess {
  table = nameNoSym "t",
  args = [
    EBinOp {
      op = OAdd (),
      lhs = EBinOp {
        op = OMul (),
        lhs = ESlice {target = x, lo = 0, hi = 1, ty = tyint 0 15, info = i},
        rhs = EInt {i = 4, ty = tyint 0 0, info = i},
        ty = tyint 0 0, info = i},
      rhs = ESlice {target = y, lo = 2, hi = 2, ty = tyint 0 3, info = i},
      ty = tyint 0 0, info = i}
  ],
  ty = TProb {info = i}, info = i
} in
utest reduceTableDimensionalityExpr e with expected using eqExpr else ppExprs in

-- x, y : (0..3, 0..3, 0..3, 1..16)
-- t(x[0], x[1], y[1], y[2], x[2]) <==> t(x[0:1] * 64 + y[1:2] * 4 + x[2])
let e = ETableAccess {
  table = nameNoSym "t",
  args = [
    ESlice {target = x, lo = 0, hi = 0, ty = tyint 0 3, info = i},
    ESlice {target = x, lo = 1, hi = 1, ty = tyint 0 3, info = i},
    ESlice {target = y, lo = 1, hi = 1, ty = tyint 0 3, info = i},
    ESlice {target = y, lo = 2, hi = 2, ty = tyint 0 3, info = i},
    ESlice {target = x, lo = 2, hi = 2, ty = tyint 0 3, info = i}
  ],
  ty = TProb {info = i}, info = i
} in
let expected = ETableAccess {
  table = nameNoSym "t",
  args = [
    EBinOp {
      op = OAdd (),
      lhs = EBinOp {
        op = OAdd (),
        lhs = EBinOp {
          op = OMul (),
          lhs = ESlice {target = x, lo = 0, hi = 1, ty = tyint 0 15, info = i},
          rhs = EInt {i = 64, ty = tyint 0 0, info = i},
          ty = tyint 0 0, info = i},
        rhs = EBinOp {
          op = OMul (),
          lhs = ESlice {target = y, lo = 1, hi = 2, ty = tyint 0 15, info = i},
          rhs = EInt {i = 4, ty = tyint 0 0, info = i},
          ty = tyint 0 0, info = i},
        ty = tyint 0 0, info = i},
      rhs = ESlice {target = x, lo = 2, hi = 2, ty = tyint 0 3, info = i},
      ty = tyint 0 0, info = i}
  ],
  ty = TProb {info = i}, info = i
} in
utest reduceTableDimensionalityExpr e with expected using eqExpr else ppExprs in

()
