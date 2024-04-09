include "utest.mc"

include "../trellis-common.mc"
include "ast.mc"
include "pprint.mc"

lang TrellisModelEqBase
  type EqOptions = {
    -- Determines whether to consider types in the equality checks.
    types : Bool
  }

  -- Checks that all elements of two sequences, which must be of the same
  -- length, are equal.
  sem allEqual : all a. all b. ((a, b) -> Bool) -> [a] -> [b] -> Bool
  sem allEqual eq l =
  | r ->
    if eqi (length l) (length r) then
      forAll eq (zip l r)
    else false
end

lang TrellisModelTypeEq = TrellisModelTypeAst + TrellisModelEqBase
  sem eqType : EqOptions -> TType -> TType -> Bool
  sem eqType options lhs =
  | rhs ->
    if options.types then eqTypeH (lhs, rhs)
    else true

  sem eqTypeH : (TType, TType) -> Bool
  sem eqTypeH =
  | (TBool _, TBool _) -> true
  | (TInt l, TInt r) -> eqBounds (l.bounds, r.bounds)
  | (TProb _, TProb _) -> true
  | (TTuple l, TTuple r) -> allEqual eqTypeH l.tys r.tys
  | (TTable l, TTable r) ->
    if eqTypeH (l.ret, r.ret) then allEqual eqTypeH l.args r.args
    else false
  | _ -> false

  sem eqBounds : (IntBound, IntBound) -> Bool
  sem eqBounds =
  | (Some l, Some r) -> if eqi l.0 r.0 then eqi l.1 r.1 else false
  | (Some _, None _) | (None _, Some _) -> false
  | (None _, None _) -> true
end

lang TrellisModelExprEq = TrellisModelExprAst + TrellisModelTypeEq
  sem eqExpr : EqOptions -> TExpr -> TExpr -> Bool
  sem eqExpr options lhs =
  | rhs ->
    if eqType options (tyTExpr lhs) (tyTExpr rhs) then
      eqExprH options (lhs, rhs)
    else false

  sem eqExprH : EqOptions -> (TExpr, TExpr) -> Bool
  sem eqExprH options =
  | (EBool l, EBool r) -> eqBool l.b r.b
  | (EVar l, EVar r) -> nameEq l.id r.id
  | (EInt l, EInt r) -> eqi l.i r.i
  | (EProb l, EProb r) -> eqf l.p r.p
  | (ESlice l, ESlice r) ->
    if eqi l.lo r.lo then
      if eqi l.hi r.hi then
        eqExpr options l.target r.target
      else false
    else false
  | (ETableAccess l, ETableAccess r) ->
    if nameEq l.table r.table then
      allEqual (lam t. eqExpr options t.0 t.1) l.args r.args
    else false
  | (EIf l, EIf r) ->
    if eqExpr options l.cond r.cond then
      if eqExpr options l.thn r.thn then
        eqExpr options l.els r.els
      else false
    else false
  | (EBinOp l, EBinOp r) ->
    if eqBinOp l.op r.op then
      if eqExpr options l.lhs r.lhs then
        eqExpr options l.rhs r.rhs
      else false
    else false
  | _ -> false

  sem eqBinOp : BOp -> BOp -> Bool
  sem eqBinOp lhs =
  | rhs -> eqi (constructorTag lhs) (constructorTag rhs)
end

lang TrellisModelSetEq = TrellisModelSetAst + TrellisModelExprEq
  sem eqSet : EqOptions -> TSet -> TSet -> Bool
  sem eqSet options lhs =
  | rhs -> eqSetH options (lhs, rhs)

  sem eqSetH : EqOptions -> (TSet, TSet) -> Bool
  sem eqSetH options =
  | (SAll _, SAll _) -> true
  | (SValueBuilder l, SValueBuilder r) ->
    if nameEq l.x r.x then
      allEqual (lam t. eqExpr options t.0 t.1) l.conds r.conds
    else false
  | (STransitionBuilder l, STransitionBuilder r) ->
    if nameEq l.x r.x then
      if nameEq l.y r.y then
        allEqual (lam t. eqExpr options t.0 t.1) l.conds r.conds
      else false
    else false
  | _ -> false
end

lang TrellisModelEq =
  TrellisModelAst + TrellisModelTypeEq + TrellisModelExprEq + TrellisModelSetEq

  sem defaultTrellisEqOptions : () -> EqOptions
  sem defaultTrellisEqOptions =
  | _ -> {types = false}

  sem trellisModelWithTypesEq : TModel -> TModel -> Bool
  sem trellisModelWithTypesEq lhs =
  | rhs -> trellisModelOptionsEq {defaultTrellisEqOptions () with types = true} lhs rhs

  sem trellisModelEq : TModel -> TModel -> Bool
  sem trellisModelEq lhs =
  | rhs -> trellisModelOptionsEq (defaultTrellisEqOptions ()) lhs rhs

  sem trellisModelOptionsEq : EqOptions -> TModel -> TModel -> Bool
  sem trellisModelOptionsEq options lhs =
  | rhs -> eqModelH options (lhs, rhs)

  sem eqModelH : EqOptions -> (TModel, TModel) -> Bool
  sem eqModelH options =
  | (lmodel, rmodel) ->
    if eqType options lmodel.stateType rmodel.stateType then
      if eqType options lmodel.outType rmodel.outType then
        if eqTables options lmodel.tables rmodel.tables then
          if eqInitialProbDef options lmodel.initial rmodel.initial then
            if eqOutputProbDef options lmodel.output rmodel.output then
              eqTransitionProbDef options lmodel.transition rmodel.transition
            else false
          else false
        else false
      else false
    else false

  sem eqTables : EqOptions -> Map Name TType -> Map Name TType -> Bool
  sem eqTables options lhs =
  | rhs -> mapEq (eqType options) lhs rhs

  sem eqInitialProbDef : EqOptions -> InitialProbDef -> InitialProbDef -> Bool
  sem eqInitialProbDef options lhs =
  | rhs ->
    if nameEq lhs.x rhs.x then allEqual (eqCase options) lhs.cases rhs.cases
    else false

  sem eqOutputProbDef : EqOptions -> OutputProbDef -> OutputProbDef -> Bool
  sem eqOutputProbDef options lhs =
  | rhs ->
    if nameEq lhs.x rhs.x then
      if nameEq lhs.o rhs.o then
        allEqual (eqCase options) lhs.cases rhs.cases
      else false
    else false

  sem eqTransitionProbDef : EqOptions -> TransitionProbDef -> TransitionProbDef -> Bool
  sem eqTransitionProbDef options lhs =
  | rhs ->
    if nameEq lhs.x rhs.x then
      if nameEq lhs.y rhs.y then
        allEqual (eqCase options) lhs.cases rhs.cases
      else false
    else false

  sem eqCase : EqOptions -> (Case, Case) -> Bool
  sem eqCase options =
  | (lc, rc) ->
    if eqSet options lc.cond rc.cond then eqExpr options lc.body rc.body
    else false
end

lang TestLang = TrellisModelEq + TrellisModelPrettyPrint end

mexpr

use TestLang in

let i = trellisInfo "trellis-eq" in
let o = {defaultTrellisEqOptions () with types = true} in
let o2 = defaultTrellisEqOptions () in
let ppTypes = lam l. lam r.
  let pp = pprintTrellisType in
  utestDefaultToString pp pp l r
in
let ppExprs = lam l. lam r.
  let pp = lam e.
    match pprintTrellisExpr pprintEnvEmpty e with (_, s) in
    s
  in
  utestDefaultToString pp pp l r
in
let ppSets = lam l. lam r.
  let pp = lam s.
    match pprintTrellisSet pprintEnvEmpty s with (_, s) in
    s
  in
  utestDefaultToString pp pp l r
in

-- Types
let ty1 = TBool {info = i} in
utest ty1 with ty1 using eqType o else ppTypes in

let ty2 = TInt {bounds = None (), info = i} in
let ty3 = TInt {bounds = Some (2, 4), info = i} in
utest ty2 with ty2 using eqType o else ppTypes in
utest ty3 with ty3 using eqType o else ppTypes in
utest eqType o ty2 ty3 with false in

let ty4 = TProb {info = i} in
utest ty4 with ty4 using eqType o else ppTypes in

let ty5 = TTuple {tys = [ty1, ty1, ty2], info = i} in
let ty6 = TTuple {tys = [ty1, ty3, ty2], info = i} in
utest ty5 with ty5 using eqType o else ppTypes in
utest ty6 with ty6 using eqType o else ppTypes in
utest eqType o ty5 ty6 with false in

let ty7 = TTable {args = [ty1, ty1], ret = ty4, info = i} in
let ty8 = TTable {args = [ty1, ty3], ret = ty4, info = i} in
utest ty7 with ty7 using eqType o else ppTypes in
utest ty8 with ty8 using eqType o else ppTypes in
utest eqType o ty7 ty8 with false in

-- Expressions
let e1 = EBool {b = false, ty = ty1, info = i} in
let e2 = EBool {b = true, ty = ty1, info = i} in
utest e1 with e1 using eqExpr o else ppExprs in
utest e2 with e2 using eqExpr o else ppExprs in
utest eqExpr o e1 e2 with false in

let e3 = EVar {id = nameNoSym "x", ty = ty1, info = i} in
let e4 = EVar {id = nameNoSym "x", ty = ty2, info = i} in
let e5 = EVar {id = nameNoSym "y", ty = ty1, info = i} in
utest e3 with e3 using eqExpr o else ppExprs in
utest e4 with e4 using eqExpr o else ppExprs in
utest e5 with e5 using eqExpr o else ppExprs in
utest eqExpr o e3 e4 with false in
utest e3 with e4 using eqExpr o2 else ppExprs in
utest eqExpr o e3 e5 with false in
utest eqExpr o2 e3 e5 with false in

let e6 = EInt {i = 2, ty = ty2, info = i} in
let e7 = EInt {i = 2, ty = ty3, info = i} in
let e8 = EInt {i = 3, ty = ty2, info = i} in
utest e6 with e6 using eqExpr o else ppExprs in
utest e7 with e7 using eqExpr o else ppExprs in
utest e8 with e8 using eqExpr o else ppExprs in
utest eqExpr o e6 e7 with false in
utest e6 with e7 using eqExpr o2 else ppExprs in
utest eqExpr o e7 e8 with false in
utest eqExpr o2 e7 e8 with false in

let e9 = EProb {p = 2.718, ty = ty4, info = i} in
let e10 = EProb {p = 3.14, ty = ty4, info = i} in
utest e9 with e9 using eqExpr o else ppExprs in
utest e10 with e10 using eqExpr o else ppExprs in
utest eqExpr o e9 e10 with false in
utest eqExpr o2 e9 e10 with false in

let e11 = EVar {id = nameNoSym "x", ty = ty5, info = i} in
let e12 = ESlice {target = e11, lo = 0, hi = 0, ty = ty1, info = i} in
let e13 = ESlice {target = e11, lo = 1, hi = 1, ty = ty1, info = i} in
let e14 = ESlice {
  target = e11, lo = 1, hi = 2, ty = TTuple {tys = [ty1, ty2], info = i},
  info = i
} in
utest e12 with e12 using eqExpr o else ppExprs in
utest e13 with e13 using eqExpr o else ppExprs in
utest e14 with e14 using eqExpr o else ppExprs in
utest eqExpr o e12 e13 with false in
utest eqExpr o2 e12 e13 with false in

let e15 = ETableAccess {
  table = nameNoSym "t", args = [], ty = ty1, info = i
} in
let e16 = ETableAccess {
  table = nameNoSym "t", args = [e6], ty = ty4, info = i
} in
let e17 = ETableAccess {
  table = nameNoSym "t", args = [e7], ty = ty4, info = i
} in
utest e15 with e15 using eqExpr o else ppExprs in
utest e16 with e16 using eqExpr o else ppExprs in
utest e17 with e17 using eqExpr o else ppExprs in
utest eqExpr o e15 e16 with false in
utest eqExpr o2 e15 e16 with false in
utest eqExpr o e16 e17 with false in
utest e16 with e17 using eqExpr o2 else ppExprs in

let e18 = EIf {cond = e1, thn = e6, els = e8, ty = ty2, info = i} in
let e19 = EIf {cond = e2, thn = e6, els = e8, ty = ty2, info = i} in
let e20 = EIf {cond = e1, thn = e7, els = e8, ty = ty2, info = i} in
let e21 = EIf {cond = e2, thn = e8, els = e6, ty = ty2, info = i} in
utest e18 with e18 using eqExpr o else ppExprs in
utest e19 with e19 using eqExpr o else ppExprs in
utest e20 with e20 using eqExpr o else ppExprs in
utest e21 with e21 using eqExpr o else ppExprs in
utest eqExpr o e18 e19 with false in
utest eqExpr o e18 e20 with false in
utest eqExpr o e19 e20 with false in
utest eqExpr o e18 e21 with false in
utest e18 with e20 using eqExpr o2 else ppExprs in

let e22 = EBinOp {op = OAdd (), lhs = e7, rhs = e7, ty = ty2, info = i} in
let e23 = EBinOp {op = OSub (), lhs = e7, rhs = e7, ty = ty2, info = i} in
let e24 = EBinOp {op = OAdd (), lhs = e6, rhs = e7, ty = ty2, info = i} in
utest e22 with e22 using eqExpr o else ppExprs in
utest e23 with e23 using eqExpr o else ppExprs in
utest e24 with e24 using eqExpr o else ppExprs in
utest eqExpr o e22 e23 with false in
utest eqExpr o e22 e24 with false in
utest eqExpr o e23 e24 with false in
utest e22 with e24 using eqExpr o2 else ppExprs in

-- Sets
let x = nameNoSym "x" in
let y = nameNoSym "y" in
let s1 = SAll {info = i} in
let s2 = SValueBuilder {x = x, conds = [e1], info = i} in
let s3 = SValueBuilder {x = x, conds = [e2], info = i} in
let s4 = STransitionBuilder {x = x, y = y, conds = [e1], info = i} in
let s5 = STransitionBuilder {x = x, y = y, conds = [e2], info = i} in
utest s1 with s1 using eqSet o else ppSets in
utest s2 with s2 using eqSet o else ppSets in
utest s3 with s3 using eqSet o else ppSets in
utest s4 with s4 using eqSet o else ppSets in
utest s5 with s5 using eqSet o else ppSets in
utest eqSet o s2 s3 with false in
utest eqSet o s4 s5 with false in

-- Model
let defaultCase = { cond = s1, body = e9 } in
let model = {
  stateType = ty1,
  outType = ty2,
  tables = mapFromSeq nameCmp [(x, ty7), (y, ty8)],
  initial = {x = x, cases = [defaultCase], info = i},
  output = {x = x, o = y, cases = [defaultCase], info = i},
  transition = {x = x, y = y, cases = [defaultCase], info = i}
} in
utest model with model using trellisModelEq in

()
