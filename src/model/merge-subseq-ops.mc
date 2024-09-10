include "../trellis-common.mc"
include "ast.mc"
include "eq.mc"
include "pprint.mc"

-- Merges subsequent operations on the same underlying target of a particular
-- shape. The current implementation can merge equality and inequality
-- operations on subsequent components of the same target tuples.
lang TrellisModelMergeSubsequentOperations = TrellisModelAst
  sem mergeSubsequentOperationsModel : TModel -> TModel
  sem mergeSubsequentOperationsModel =
  | {transition = t} & model ->
    let transition = {t with cases = map mergeSubsequentOperationsCase t.cases} in
    {model with transition = transition}

  sem mergeSubsequentOperationsCase : TCase -> TCase
  sem mergeSubsequentOperationsCase =
  | c -> {c with cond = mergeSubsequentOperationsSet c.cond}

  sem mergeSubsequentOperationsSet : TSet -> TSet
  sem mergeSubsequentOperationsSet =
  | SAll t -> SAll t
  | STransitionBuilder t ->
    STransitionBuilder {t with conds = foldl mergeSubsequentOperations [] t.conds}

  sem mergeSubsequentOperations : [TExpr] -> TExpr -> [TExpr]
  sem mergeSubsequentOperations acc =
  | e & (ESlice {target = EVar {id = id}, lo = idx}) ->
    match acc with a ++ [
      ESlice (t & {target = EVar {id = id2}, lo = lidx, hi = hidx})
    ] then
      if nameEq id id2 then
        match
          if eqi (addi idx 1) lidx then Some (idx, hidx)
          else if eqi idx (addi hidx 1) then Some (lidx, idx)
          else None ()
        with Some (lo, hi) then
          let ty = sliceType lo hi (tyTExpr t.target) in
          snoc a (ESlice {t with lo = lo, hi = hi, ty = ty})
        else snoc acc e
      else snoc acc e
    else snoc acc e
  | e & (EBinOp {
      op = op & (OEq _ | ONeq _),
      lhs = ESlice {target = EVar {id = lid}, lo = lidx},
      rhs = ESlice {target = EVar {id = rid}, lo = ridx} }) ->
    match acc with a ++ [
      EBinOp (t & {
        op = op2 & (OEq _ | ONeq _),
        lhs = ESlice (lt & {target = EVar {id = lid2}, lo = ll, hi = lh}),
        rhs = ESlice (rt & {target = EVar {id = rid2}, lo = rl, hi = rh})})
    ] then
      if and (eqi (constructorTag op) (constructorTag op2))
             (and (nameEq lid lid2) (nameEq rid rid2)) then
        match
          if and (eqi (addi lidx 1) ll) (eqi (addi ridx 1) rl) then
            Some (lidx, lh, ridx, rh)
          else if and (eqi (addi lh 1) lidx) (eqi (addi rh 1) ridx) then
            Some (ll, lidx, rl, ridx)
          else None ()
        with Some (ll, lh, rl, rh) then
          let lty = sliceType ll lh (tyTExpr lt.target) in
          let rty = sliceType rl rh (tyTExpr rt.target) in
          snoc a (EBinOp {t with lhs = ESlice {lt with lo = ll, hi = lh, ty = lty},
                                 rhs = ESlice {rt with lo = rl, hi = rh, ty = rty}})
        else snoc acc e
      else snoc acc e
    else snoc acc e
  | e -> snoc acc e
end

lang TestLang =
  TrellisModelMergeSubsequentOperations + TrellisModelEq +
  TrellisModelPrettyPrint
end

mexpr

use TestLang in

let ppSets = lam l. lam r.
  let pp = lam s. match pprintTrellisSet pprintEnvEmpty s with (_, s) in s in
  utestDefaultToString pp pp l r
in
let eqSet = eqSet (defaultTrellisEqOptions ()) in

let i = trellisInfo "trellis-merge-subsequent-ops" in
let ty = TTuple {tys = create 5 (lam. TBool {info = i}), info = i} in
let xid = nameNoSym "x" in
let yid = nameNoSym "y" in
let x = EVar {id = xid, ty = ty, info = i} in
let y = EVar {id = yid, ty = ty, info = i} in
let setOfConds = lam conds.
  STransitionBuilder { x = xid, y = yid, conds = conds, info = i }
in
let bop = lam op. lam l. lam r.
  EBinOp {op = op, lhs = l, rhs = r, ty = TBool {info = i}, info = i}
in
let eq = lam l. lam r. bop (OEq ()) l r in
let neq = lam l. lam r. bop (ONeq ()) l r in
let slice = lam t. lam l. lam h.
  let sliceTy = sliceType l h (tyTExpr t) in
  ESlice {target = t, lo = l, hi = h, ty = sliceTy, info = i}
in

-- x[0] == y[0], x[1] == y[1] <==> x[0:1] == y[0:1]
let s = setOfConds [
  eq (slice x 0 0) (slice y 0 0),
  eq (slice x 1 1) (slice y 1 1)
] in
let expected = setOfConds [
  eq (slice x 0 1) (slice y 0 1)
] in
utest mergeSubsequentOperationsSet s with expected using eqSet else ppSets in

-- x[1] == y[1], x[0] == y[0], x[2] == y[2] <==> x[0:2] == y[0:2]
let s = setOfConds [
  eq (slice x 1 1) (slice y 1 1),
  eq (slice x 0 0) (slice y 0 0),
  eq (slice x 2 2) (slice y 2 2)
] in
let expected = setOfConds [
  eq (slice x 0 2) (slice y 0 2)
] in
utest mergeSubsequentOperationsSet s with expected using eqSet else ppSets in

-- x[0] == y[0], x[1] == y[1], x[3] == y[2], x[4] == y[3]
-- <==>
-- x[0:1] == y[0:1], x[3:4] == y[2:3]
let s = setOfConds [
  eq (slice x 0 0) (slice y 0 0),
  eq (slice x 1 1) (slice y 1 1),
  eq (slice x 3 3) (slice y 2 2),
  eq (slice x 4 4) (slice y 3 3)
] in
let expected = setOfConds [
  eq (slice x 0 1) (slice y 0 1),
  eq (slice x 3 4) (slice y 2 3)
] in
utest mergeSubsequentOperationsSet s with expected using eqSet else ppSets in

-- x[0] == y[0], x[1] != y[1], x[2] != y[2], x[3] == y[3]
-- <==>
-- x[0] == y[0], x[1:2] != y[1:2], x[3] == y[3]
let s = setOfConds [
  eq (slice x 0 0) (slice y 0 0),
  neq (slice x 1 1) (slice y 1 1),
  neq (slice x 2 2) (slice y 2 2),
  eq (slice x 3 3) (slice y 3 3)
] in
let expected = setOfConds [
  eq (slice x 0 0) (slice y 0 0),
  neq (slice x 1 2) (slice y 1 2),
  eq (slice x 3 3) (slice y 3 3)
] in
utest mergeSubsequentOperationsSet s with expected using eqSet else ppSets in

-- NOTE(larshum, 2024-04-26): Below, we test the merging on direct slice
-- expressions. These are not valid to use in a set, but this form of
-- construction makes things easier.

-- x[0], x[1], x[2]
-- <==>
-- x[0:2]
let s = setOfConds [
  slice x 0 0,
  slice x 1 1,
  slice x 2 2
] in
let expected = setOfConds [slice x 0 2] in
utest mergeSubsequentOperationsSet s with expected using eqSet else ppSets in

-- x[1], x[2], x[0]
-- <==>
-- x[0:2]
let s = setOfConds [
  slice x 1 1,
  slice x 2 2,
  slice x 0 0
] in
let expected = setOfConds [slice x 0 2] in
utest mergeSubsequentOperationsSet s with expected using eqSet else ppSets in

()
