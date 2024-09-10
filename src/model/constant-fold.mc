-- Defines constant folding on the Trellis model AST, by simplifying operations
-- on constant values.

include "math.mc"

include "ast.mc"
include "encode.mc"
include "eq.mc"
include "pprint.mc"
include "../trellis-common.mc"

lang TrellisConstantFoldExpr = TrellisModelAst + TrellisEncode
  type UnOpRec = {op : UOp, target : TExpr, ty : TType, info : Info}
  type BinOpRec = {lhs : TExpr, rhs : TExpr, op : BOp, ty : TType, info : Info}

  sem constantFold : TExpr -> TExpr
  sem constantFold =
  | EUnOp t -> constantFoldUnaryOperation t
  | EBinOp t -> constantFoldBinaryOperation t
  | e -> smapTExprTExpr constantFold e

  sem constantFoldUnaryOperation : UnOpRec -> TExpr
  sem constantFoldUnaryOperation =
  | t ->
    let target = constantFold t.target in
    switch t.op
    case ONot _ then
      match target with EBool tt then
        EBool {tt with b = not tt.b}
      else EUnOp {t with target = target}
    end

  sem constantFoldBinaryOperation : BinOpRec -> TExpr
  sem constantFoldBinaryOperation =
  | t ->
    let lhs = constantFold t.lhs in
    let rhs = constantFold t.rhs in
    switch t.op
    case OAdd _ | OSub _ | OMul _ | ODiv _ | OMod _ then
      constantFoldArithmeticOperation t (lhs, rhs)
    case OEq _ | ONeq _ | OLt _ | OGt _ | OLeq _ | OGeq _ then
      constantFoldComparisonOperation t (lhs, rhs)
    case OAnd _ | OOr _ then
      constantFoldBooleanOperation t (lhs, rhs)
    case _ then
      EBinOp {t with lhs = lhs, rhs = rhs}
    end

  -- NOTE(larshum, 2024-04-22): In our lifting of constant values, we return
  -- this to indicate that the non-constant part of the expression is empty. We
  -- always have to check for this value to prevent it from leaking outside of
  -- the constant folding.
  syn TExpr =
  | EEmpty ()

  sem liftConstants : Int -> TExpr -> (TExpr, Int)
  sem liftConstants n =
  | EInt t -> (EEmpty (), addi n t.i)
  | EBinOp t ->
    switch (t.lhs, t.rhs)
    case (EInt {i = li}, EInt {i = ri}) then
      (EEmpty (), addi n (intOperation t.op li ri))
    case (EInt {i = li}, _) then
      liftConstants (addi n li) t.rhs
    case (_, EInt {i = ri}) then
      liftConstants (intOperation t.op n ri) t.lhs
    case (_, _) then
      match liftConstants n t.lhs with (lhs, n) in
      match liftConstants n t.rhs with (rhs, n) in
      (EBinOp {t with lhs = lhs, rhs = rhs}, n)
    end
  | e -> (e, n)

  -- Determines if a given expression does not perform any operations but
  -- addition and subtraction of literals and variables of integer type.
  sem onlyPerformsAddSub : TExpr -> Bool
  sem onlyPerformsAddSub =
  | EVar _ | EInt _ | ESlice _ -> true
  | EBinOp {op = OAdd _ | OSub _, lhs = lhs, rhs = rhs} ->
    and (onlyPerformsAddSub lhs) (onlyPerformsAddSub rhs)
  | _ -> false

  sem constantFoldArithmeticOperation : BinOpRec -> (TExpr, TExpr) -> TExpr
  sem constantFoldArithmeticOperation t =
  | (EInt {i = li}, EInt {i = ri}) ->
    EInt {i = intOperation t.op li ri, ty = t.ty, info = t.info}
  | (EProb {p = lp}, EProb {p = rp}) ->
    EProb {p = probOperation t.op t.info lp rp, ty = t.ty, info = t.info}
  | (l, r) ->
    let e = EBinOp {t with lhs = l, rhs = r} in
    match (tyTExpr l, onlyPerformsAddSub e)
    with (TInt _, true) then
      match liftConstants 0 e with (e, n) in
      let cexpr =
        EInt {i = n, ty = TInt {bounds = None (), info = t.info}, info = t.info}
      in
      match e with EEmpty _ then cexpr
      else if eqi n 0 then e
      else EBinOp {t with op = OAdd (), lhs = e, rhs = cexpr}
    else e

  sem intOperation : BOp -> (Int -> Int -> Int)
  sem intOperation =
  | OAdd _ -> addi
  | OSub _ -> subi
  | OMul _ -> muli
  | ODiv _ -> divi
  | OMod _ -> modi

  sem probOperation : BOp -> (Info -> Float -> Float -> Float)
  sem probOperation =
  | OMul _ -> lam. lam l. lam r. exp (addf (log l) (log r))
  | ODiv _ -> lam. lam l. lam r. exp (subf (log l) (log r))
  | OMod _ -> lam i. errorSingle [i] "Modulo not supported on probabilities"

  sem constantFoldComparisonOperation : BinOpRec -> (TExpr, TExpr) -> TExpr
  sem constantFoldComparisonOperation t =
  | (lhs, rhs) ->
    let intExpr = lam n.
      EInt {i = n, ty = TInt {bounds = None (), info = t.info}, info = t.info}
    in
    -- NOTE(larshum, 2024-04-22): For comparison operations (on integers) where
    -- the only binary operations performed by either side is addition and
    -- subtraction, we compute a combined literal value and move this to the
    -- right-hand side of the comparison.
    match (tyTExpr lhs, onlyPerformsAddSub lhs, onlyPerformsAddSub rhs)
    with (TInt _, true, true) then
      match liftConstants 0 lhs with (lhs, ln) in
      match liftConstants 0 rhs with (rhs, rn) in
      let n = subi rn ln in
      let lhs =
        match lhs with EEmpty _ then intExpr 0
        else lhs
      in
      let rhs =
        match rhs with EEmpty _ then intExpr n
        else if eqi n 0 then rhs
        else
          EBinOp {
            op = OAdd (), lhs = rhs,
            rhs = EInt {
              i = n, ty = TInt {bounds = None (), info = t.info},
              info = t.info},
            ty = tyTExpr rhs, info = t.info }
      in
      constantFoldBooleanOperation t (lhs, rhs)
    else constantFoldBooleanOperation t (lhs, rhs)

  sem constantFoldBooleanOperation : BinOpRec -> (TExpr, TExpr) -> TExpr
  sem constantFoldBooleanOperation t =
  | (EBool {b = lb}, EBool {b = rb}) ->
    EBool {b = boolOperation t.op lb rb, ty = t.ty, info = t.info}
  | (EInt {i = li}, EInt {i = ri}) ->
    EBool {b = intBoolOperation t.op li ri, ty = t.ty, info = t.info}
  | (EProb {p = lp}, EProb {p = rp}) ->
    EBool {b = probBoolOperation t.op lp rp, ty = t.ty, info = t.info}
  | (l, r) -> EBinOp {t with lhs = l, rhs = r}

  sem boolOperation : BOp -> (Bool -> Bool -> Bool)
  sem boolOperation =
  | OEq _ -> eqBool
  | ONeq _ -> xor
  | OAnd _ -> and
  | OOr _ -> or

  sem intBoolOperation : BOp -> (Int -> Int -> Bool)
  sem intBoolOperation =
  | OEq _ -> eqi
  | ONeq _ -> neqi
  | OLt _ -> lti
  | OGt _ -> gti
  | OLeq _ -> leqi
  | OGeq _ -> geqi

  sem probBoolOperation : BOp -> (Float -> Float -> Bool)
  sem probBoolOperation =
  | OEq _ -> eqf
  | ONeq _ -> neqf
  | OLt _ -> ltf
  | OGt _ -> gtf
  | OLeq _ -> leqf
  | OGeq _ -> geqf
end

-- Defines constant folding on the model AST components containing expressions
-- by using the definition on expressions above.
lang TrellisConstantFold = TrellisConstantFoldExpr
  sem constantFoldModel : TModel -> TModel
  sem constantFoldModel =
  | model & {initial = i, output = o, transition = t} ->
    {model with initial = {i with body = constantFold i.body},
                output = {o with body = constantFold o.body},
                transition = {t with cases = map constantFoldCase t.cases}}

  sem constantFoldCase : TCase -> TCase
  sem constantFoldCase =
  | c -> {c with cond = constantFoldSet c.cond, body = constantFold c.body}

  sem constantFoldSet : TSet -> TSet
  sem constantFoldSet =
  | s -> smapTSetTExpr constantFold s
end

lang TestLang =
  TrellisConstantFoldExpr + TrellisModelPrettyPrint + TrellisModelEq
end

mexpr

use TestLang in

let eqExpr = eqExpr (defaultTrellisEqOptions ()) in
let eqProbExpr = lam l. lam r.
  match l with EProb {p = p} then
    eqfApprox 1e-6 p r
  else false
in

let ppExprs = lam l. lam r.
  let pp = lam e.
    match pprintTrellisExpr pprintEnvEmpty e with (_, s) in
    s
  in
  utestDefaultToString pp pp l r
in

let i = trellisInfo "constant-fold" in

let tbool = TBool {info = i} in
let tint = TInt {bounds = None (), info = i} in
let tprob = TProb {info = i} in
let bool = lam b. EBool {b = b, ty = tbool, info = i} in
let int = lam x. EInt {i = x, ty = tint, info = i} in
let prob = lam x. EProb {p = x, ty = tprob, info = i} in

let bop = lam o. lam l. lam r. lam ty.
  EBinOp {op = o, lhs = l, rhs = r, ty = ty, info = i}
in

-- Booleans
let notexpr = lam b.
  EUnOp {op = ONot (), target = b, ty = tbool, info = i}
in
utest constantFold (bool false) with bool false using eqExpr else ppExprs in
utest constantFold (bool true) with bool true using eqExpr else ppExprs in
utest constantFold (notexpr (bool false)) with bool true
using eqExpr else ppExprs in
utest constantFold (notexpr (bool true)) with bool false
using eqExpr else ppExprs in

utest constantFold (bop (OEq ()) (bool true) (bool true) tbool) with bool true
using eqExpr else ppExprs in
utest constantFold (bop (ONeq ()) (bool true) (bool false) tbool) with bool true
using eqExpr else ppExprs in
utest constantFold (bop (OAnd ()) (bool true) (bool false) tbool) with bool false
using eqExpr else ppExprs in
utest constantFold (bop (OOr ()) (bool true) (bool false) tbool) with bool true
using eqExpr else ppExprs in

-- Integers
utest constantFold (int 2) with int 2 using eqExpr else ppExprs in
utest constantFold (bop (OAdd ()) (int 7) (int 3) tint) with int 10
using eqExpr else ppExprs in
utest constantFold (bop (OSub ()) (int 7) (int 3) tint) with int 4
using eqExpr else ppExprs in
utest constantFold (bop (OMul ()) (int 7) (int 3) tint) with int 21
using eqExpr else ppExprs in
utest constantFold (bop (ODiv ()) (int 7) (int 3) tint) with int 2
using eqExpr else ppExprs in
utest constantFold (bop (OMod ()) (int 7) (int 3) tint) with int 1
using eqExpr else ppExprs in
utest constantFold (bop (OEq ()) (int 7) (int 3) tbool) with bool false
using eqExpr else ppExprs in
utest constantFold (bop (ONeq ()) (int 7) (int 3) tbool) with bool true
using eqExpr else ppExprs in
utest constantFold (bop (OLt ()) (int 7) (int 3) tbool) with bool false
using eqExpr else ppExprs in
utest constantFold (bop (OGt ()) (int 7) (int 3) tbool) with bool true
using eqExpr else ppExprs in
utest constantFold (bop (OLeq ()) (int 7) (int 3) tbool) with bool false
using eqExpr else ppExprs in
utest constantFold (bop (OGeq ()) (int 7) (int 3) tbool) with bool true
using eqExpr else ppExprs in

let expr =
  bop (OEq ())
    (bop (OSub ()) (int 1) (int 3) tint)
    (bop (OSub ()) (int 3) (bop (OAdd ()) (int 2) (int 3) tint) tint)
    tbool
in
utest constantFold expr with bool true using eqExpr else ppExprs in

-- Probabilities
utest constantFold (prob 0.5) with prob 0.5 using eqExpr else ppExprs in
utest constantFold (bop (OMul ()) (prob 0.4) (prob 0.5) tprob) with prob 0.2
using eqExpr else ppExprs in
utest constantFold (bop (ODiv ()) (prob 0.4) (prob 0.5) tprob) with prob 0.8
using eqExpr else ppExprs in
utest constantFold (bop (OEq ()) (prob 0.4) (prob 0.5) tbool) with bool false
using eqExpr else ppExprs in
utest constantFold (bop (ONeq ()) (prob 0.4) (prob 0.5) tbool) with bool true
using eqExpr else ppExprs in
utest constantFold (bop (OLt ()) (prob 0.4) (prob 0.5) tbool) with bool true
using eqExpr else ppExprs in
utest constantFold (bop (OGt ()) (prob 0.4) (prob 0.5) tbool) with bool false
using eqExpr else ppExprs in
utest constantFold (bop (OLeq ()) (prob 0.4) (prob 0.5) tbool) with bool true
using eqExpr else ppExprs in
utest constantFold (bop (OGeq ()) (prob 0.4) (prob 0.5) tbool) with bool false
using eqExpr else ppExprs in

-- Expressions including statically unknown variables
let var = lam x. lam ty. EVar {id = nameNoSym x, ty = ty, info = i} in
let nested1 =
  bop (OAdd ()) (var "x" tint) (bop (OMul ()) (int 2) (int 3) tint) tint
in
let expected = bop (OAdd ()) (var "x" tint) (int 6) tint in
utest constantFold nested1 with expected using eqExpr else ppExprs in

let nested2 =
  bop (OAdd ()) (int 2) (bop (OMul ()) (var "x" tint) (int 3) tint) tint
in
utest constantFold nested2 with nested2 using eqExpr else ppExprs in

let expr =
  bop (OEq ())
    (bop (OAdd ()) (var "x" tint) (int 2) tint)
    (bop (OAdd ()) (var "y" tint) (int 1) tint)
    tbool
in
let expected =
  bop (OEq ()) (var "x" tint) (bop (OAdd ()) (var "y" tint) (int -1) tint) tbool
in
utest constantFold expr with expected using eqExpr else ppExprs in

let expr =
  bop (OEq ()) (bop (OAdd ()) (var "x" tint) (int 2) tint) (int 2) tbool
in
let expected = bop (OEq ()) (var "x" tint) (int 0) tbool in
utest constantFold expr with expected using eqExpr else ppExprs in

let expr =
  bop (ONeq ()) (var "x" tint) (var "y" tint) tbool
in
utest constantFold expr with expr using eqExpr else ppExprs in

let expr =
  bop (OLt ())
    (bop (OAdd ()) (int 1) (bop (OAdd ()) (var "x" tint) (int 2) tint) tint)
    (bop (OAdd ()) (var "y" tint) (int 4) tint)
    tbool
in
let expected =
  bop (OLt ()) (var "x" tint) (bop (OAdd ()) (var "y" tint) (int 1) tint) tbool
in
utest constantFold expr with expected using eqExpr else ppExprs in

let expr =
  bop (OEq ()) (var "x" tint) (bop (OAdd ()) (int 2) (int 3) tint) tbool
in
let expected = bop (OEq ()) (var "x" tint) (int 5) tbool in
utest constantFold expr with expected using eqExpr else ppExprs in

()
