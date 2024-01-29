include "math.mc"

include "ast.mc"
include "encode.mc"
include "pprint.mc"
include "../trellis-common.mc"

lang TrellisConstantFold = TrellisModelAst + TrellisEncode
  type OpRec = {lhs : TExpr, rhs : TExpr, op : BOp, ty : TType, info : Info}

  sem constantFold : TExpr -> TExpr
  sem constantFold =
  | EIf t ->
    let cond = constantFold t.cond in
    let thn = constantFold t.thn in
    let els = constantFold t.els in
    match cond with EBool {b = b} then
      if b then thn else els
    else
      EIf {t with cond = cond, thn = thn, els = els}
  | EBinOp t -> constantFoldOperation t
  | e -> smapTExprTExpr constantFold e

  sem constantFoldOperation : OpRec -> TExpr
  sem constantFoldOperation =
  | t ->
    let lhs = constantFold t.lhs in
    let rhs = constantFold t.rhs in
    let t = {t with lhs = constantFold t.lhs, rhs = constantFold t.rhs} in
    switch t.op
    case OAdd _ | OSub _ | OMul _ | ODiv _ | OMod _ then
      constantFoldArithOperation t (lhs, rhs)
    case OEq _ | ONeq _ | OLt _ | OGt _ | OLeq _ | OGeq _ | OAnd _ | OOr _ then
      constantFoldBoolOperation t (lhs, rhs)
    case _ then
      EBinOp t
    end

  sem constantFoldArithOperation : OpRec -> (TExpr, TExpr) -> TExpr
  sem constantFoldArithOperation t =
  | (EInt {i = li}, EInt {i = ri}) ->
    EInt {i = intOperation t.op li ri, ty = t.ty, info = t.info}
  | (EProb {p = lp}, EProb {p = rp}) ->
    EProb {p = probOperation t.op t.info lp rp, ty = t.ty, info = t.info}
  | (l, r) -> EBinOp {t with lhs = l, rhs = r}

  sem intOperation : BOp -> (Int -> Int -> Int)
  sem intOperation =
  | OAdd _ -> addi
  | OSub _ -> subi
  | OMul _ -> muli
  | ODiv _ -> divi
  | OMod _ -> modi

  sem probOperation : BOp -> (Info -> Float -> Float -> Float)
  sem probOperation =
  | OAdd _ -> lam. lam l. lam r. log (addf l r)
  | OSub _ -> lam. lam l. lam r. log (subf l r)
  | OMul _ -> lam. lam l. lam r. exp (addf (log l) (log r))
  | ODiv _ -> lam. lam l. lam r. exp (subf (log l) (log r))
  | OMod _ -> lam i. errorSingle [i] "Modulo not supported on probabilities"

  sem constantFoldBoolOperation : OpRec -> (TExpr, TExpr) -> TExpr
  sem constantFoldBoolOperation t =
  | (EBool {b = lb}, EBool {b = rb}) ->
    EBool {b = boolOperation t.op lb rb,
           ty = TBool {info = t.info}, info = t.info}
  | (EInt {i = li}, EInt {i = ri}) ->
    EBool {b = intBoolOperation t.op li ri,
           ty = TBool {info = t.info}, info = t.info}
  | (EProb {p = lp}, EProb {p = rp}) ->
    EBool {b = probBoolOperation t.op lp rp,
           ty = TBool {info = t.info}, info = t.info}

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

lang TestLang = TrellisConstantFold + TrellisModelPrettyPrint
end

mexpr

use TestLang in

let pprintTestExpr = lam e.
  let e = constantFold e in
  match pprintTrellisExpr pprintEnvEmpty e with (_, s) in s
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
let ifexpr = lam c. lam t. lam e.
  EIf {cond = c, thn = t, els = e, ty = tbool, info = i}
in
utest pprintTestExpr (bool false) with "false" using eqString else ppStrings in
utest pprintTestExpr (bool true) with "true" using eqString else ppStrings in
utest pprintTestExpr (ifexpr (bool false) (int 1) (int 2)) with "2"
using eqString else ppStrings in
utest pprintTestExpr (ifexpr (bool true) (int 1) (int 2)) with "1"
using eqString else ppStrings in

utest pprintTestExpr (bop (OEq ()) (bool true) (bool true) tbool) with "true"
using eqString else ppStrings in
utest pprintTestExpr (bop (ONeq ()) (bool true) (bool false) tbool) with "true"
using eqString else ppStrings in
utest pprintTestExpr (bop (OAnd ()) (bool true) (bool false) tbool) with "false"
using eqString else ppStrings in
utest pprintTestExpr (bop (OOr ()) (bool true) (bool false) tbool) with "true"
using eqString else ppStrings in

-- Integers
utest pprintTestExpr (int 2) with "2" using eqString else ppStrings in
utest pprintTestExpr (bop (OAdd ()) (int 7) (int 3) tint) with "10"
using eqString else ppStrings in
utest pprintTestExpr (bop (OSub ()) (int 7) (int 3) tint) with "4"
using eqString else ppStrings in
utest pprintTestExpr (bop (OMul ()) (int 7) (int 3) tint) with "21"
using eqString else ppStrings in
utest pprintTestExpr (bop (ODiv ()) (int 7) (int 3) tint) with "2"
using eqString else ppStrings in
utest pprintTestExpr (bop (OMod ()) (int 7) (int 3) tint) with "1"
using eqString else ppStrings in
utest pprintTestExpr (bop (OEq ()) (int 7) (int 3) tbool) with "false"
using eqString else ppStrings in
utest pprintTestExpr (bop (ONeq ()) (int 7) (int 3) tbool) with "true"
using eqString else ppStrings in
utest pprintTestExpr (bop (OLt ()) (int 7) (int 3) tbool) with "false"
using eqString else ppStrings in
utest pprintTestExpr (bop (OGt ()) (int 7) (int 3) tbool) with "true"
using eqString else ppStrings in
utest pprintTestExpr (bop (OLeq ()) (int 7) (int 3) tbool) with "false"
using eqString else ppStrings in
utest pprintTestExpr (bop (OGeq ()) (int 7) (int 3) tbool) with "true"
using eqString else ppStrings in

-- Probabilities
utest pprintTestExpr (prob 0.5) with "0.5" using eqString else ppStrings in
utest pprintTestExpr (bop (OAdd ()) (prob 0.4) (prob 0.5) tprob) with "-0.105360515658"
using eqString else ppStrings in
utest pprintTestExpr (bop (OSub ()) (prob 0.5) (prob 0.4) tprob) with "-2.30258509299"
using eqString else ppStrings in
utest pprintTestExpr (bop (OMul ()) (prob 0.4) (prob 0.5) tprob) with "0.2"
using eqString else ppStrings in
utest pprintTestExpr (bop (ODiv ()) (prob 0.4) (prob 0.5) tprob) with "0.8"
using eqString else ppStrings in
utest pprintTestExpr (bop (OEq ()) (prob 0.4) (prob 0.5) tbool) with "false"
using eqString else ppStrings in
utest pprintTestExpr (bop (ONeq ()) (prob 0.4) (prob 0.5) tbool) with "true"
using eqString else ppStrings in
utest pprintTestExpr (bop (OLt ()) (prob 0.4) (prob 0.5) tbool) with "true"
using eqString else ppStrings in
utest pprintTestExpr (bop (OGt ()) (prob 0.4) (prob 0.5) tbool) with "false"
using eqString else ppStrings in
utest pprintTestExpr (bop (OLeq ()) (prob 0.4) (prob 0.5) tbool) with "true"
using eqString else ppStrings in
utest pprintTestExpr (bop (OGeq ()) (prob 0.4) (prob 0.5) tbool) with "false"
using eqString else ppStrings in

-- Expressions with unresolved variables
let var = lam x. lam ty. EVar {id = nameNoSym x, ty = ty, info = i} in
let nested1 =
  bop (OAdd ()) (var "x" tint) (bop (OMul ()) (int 2) (int 3) tint) tint
in
utest pprintTestExpr nested1 with "(x + 6)" using eqString else ppStrings in

let nested2 =
  bop (OAdd ()) (int 2) (bop (OMul ()) (var "x" tint) (int 3) tint) tint
in
utest pprintTestExpr nested2 with "(2 + (x * 3))" using eqString else ppStrings in

-- TODO: nested expressions using more than one of the above categories...

()
