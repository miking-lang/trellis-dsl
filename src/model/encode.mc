include "mexpr/info.mc"

include "ast.mc"
include "pprint.mc"
include "../trellis-common.mc"

lang TrellisTypeBitwidth = TrellisModelAst
  -- Finds the number of bits needed to represent integers from zero to n.
  sem findBitwidth : Int -> Int
  sem findBitwidth =
  | 1 -> 1
  | n ->
    recursive let work = lam count. lam i.
      if lti i n then work (addi count 1) (slli i 1)
      else count
    in work 0 1

  -- Computes the number of bits needed to represent all possible values of a
  -- given type. Infinite types result in an error.
  sem bitwidthType : TType -> Int
  sem bitwidthType =
  | TBool _ -> 1
  | TInt {bounds = Some (lb, ub)} -> findBitwidth (addi (subi ub lb) 1)
  | TTuple {tys = tys} -> foldl addi 0 (map bitwidthType tys)
  | TInt {bounds = None _, info = info} | TProb {info = info} ->
    errorSingle [info] "Cannot compute the bitwidth of an infinite type"
  | TTable {info = info} ->
    errorSingle [info] "Cannot compute the bitwidth of a table type"
end

lang TrellisTypeCardinality = TrellisModelAst
  -- Computes the number of distinct values a finite type can have
  -- (cardinality). Infinite types result in an error.
  sem cardinalityType : TType -> Int
  sem cardinalityType =
  | TBool _ -> 2
  | TInt {bounds = Some (lo, hi)} -> addi (subi hi lo) 1
  | TTuple {tys = tys} -> foldl muli 1 (map cardinalityType tys)
  | TInt {bounds = None _, info = info} | TProb {info = info} ->
    errorSingle [info] "Cannot compute the cardinality of an infinite type"
  | TTable {info = info} ->
    errorSingle [info] "Cannot compute the cardinality of a table type"
end

lang TrellisEncodeBase = TrellisModelExprPrettyPrint + TrellisModelAst
  sem pprintBinOp =
end

lang TrellisEncodeMixedRadix = TrellisEncodeBase + TrellisTypeCardinality
  syn BOp =
  | OMod ()

  sem pprintBinOp =
  | OMod _ -> "%"

  sem generateMixedRadixOperations : Info -> [TType] -> Int -> Int -> TExpr -> TExpr
  sem generateMixedRadixOperations info tys lo hi =
  | target ->
    let cards = map cardinalityType tys in
    let div = foldl muli 1 (subsequence cards (addi hi 1) (length tys)) in
    let sliceCards = subsequence cards lo (addi (subi hi lo) 1) in
    let mod = foldl muli 1 sliceCards in
    let totCard = foldl1 muli cards in
    let resultTy = TInt {bounds = Some (0, totCard), info = info} in
    applyModulo info resultTy mod
      (applyDivision info resultTy div target)

  sem applyModulo : Info -> TType -> Int -> TExpr -> TExpr
  sem applyModulo info ty mod =
  | e ->
    let rhs = EInt {i = mod, ty = ty, info = info} in
    EBinOp {op = OMod (), lhs = e, rhs = rhs, ty = ty, info = info}

  sem applyDivision : Info -> TType -> Int -> TExpr -> TExpr
  sem applyDivision info ty div =
  | e ->
    if eqi div 1 then e else
    let rhs = EInt {i = div, ty = ty, info = info} in
    EBinOp {op = ODiv (), lhs = e, rhs = rhs, ty = ty, info = info}
end

lang TrellisEncodeExpr = TrellisEncodeMixedRadix
  sem encodeStateOperationsExpr : TExpr -> TExpr
  sem encodeStateOperationsExpr =
  | EVar t ->
    match t.ty with TTable _ then EVar t
    else
      let maxsz = cardinalityType t.ty in
      let ty = TInt {bounds = Some (0, maxsz), info = t.info} in
      EVar {t with ty = ty}
  | ESlice {target = target, lo = lo, hi = hi, ty = ty, info = info} ->
    if lti hi lo then errorSingle [info] "Invalid slice node" else
    let targetTy = tyTExpr target in
    let target = encodeStateOperationsExpr target in
    match targetTy with TTuple {tys = tys} then
      generateMixedRadixOperations info tys lo hi target
    else errorSingle [info] "Projection has invalid type"
  | e -> smapTExprTExpr encodeStateOperationsExpr e
end

lang TrellisEncode = TrellisEncodeExpr
  sem encodeStateOperations : TrellisOptions -> TModel -> TModel
  sem encodeStateOperations options =
  | model & {initial = i, output = o, transition = t} ->
    let encCase = encodeStateOperationsCase options in
    {model with initial = {i with cases = map encCase i.cases},
                output = {o with cases = map encCase o.cases},
                transition = {t with cases = map encCase t.cases}}

  sem encodeStateOperationsCase : TrellisOptions -> Case -> Case
  sem encodeStateOperationsCase options =
  | {cond = cond, body = body} ->
    let encExpr = encodeStateOperationsExpr in
    { cond = smapTSetTExpr encExpr cond
    , body = encExpr body }
end

lang TestLang = TrellisEncode + TrellisModelPrettyPrint + TrellisTypeBitwidth
end

mexpr

use TestLang in

let pprintExpr = lam e.
  match pprintTrellisExpr pprintEnvEmpty e with (_, s) in s
in

utest findBitwidth 0 with 0 in
utest findBitwidth 1 with 1 in
utest findBitwidth 2 with 1 in
utest findBitwidth 3 with 2 in
utest findBitwidth 12 with 4 in
utest findBitwidth 16 with 4 in
utest findBitwidth 100 with 7 in

let i = trellisInfo "trellis-encode" in
let ty1 = TBool {info = i} in
let ty2 = TInt {bounds = Some (2, 7), info = i} in
let ty3 = TInt {bounds = Some (0, 100), info = i} in
let ty4 = TTuple {tys = [ty1, ty2, ty3], info = i} in
utest bitwidthType ty1 with 1 in
utest bitwidthType ty2 with 3 in
utest bitwidthType ty3 with 7 in
utest bitwidthType ty4 with 11 in

utest cardinalityType ty1 with 2 in
utest cardinalityType ty2 with 6 in
utest cardinalityType ty3 with 101 in
utest cardinalityType ty4 with 1212 in

let ty = TTuple {tys = [ty2, ty2, ty1], info = i} in
let x = EVar {id = nameNoSym "x", ty = ty, info = i} in
let proj = lam idx. ESlice {target = x, lo = idx, hi = idx, ty = ty2, info = i} in

utest pprintExpr (encodeStateOperationsExpr (proj 0))
with "((x / 12) % 6)" using eqString else ppStrings in
utest pprintExpr (encodeStateOperationsExpr (proj 1))
with "((x / 2) % 6)" using eqString else ppStrings in
utest pprintExpr (encodeStateOperationsExpr (proj 2))
with "(x % 2)" using eqString else ppStrings in

let slice = ESlice {
  target = x, lo = 0, hi = 1, ty = TTuple {tys = [ty2, ty2], info = i}, info = i
} in
utest pprintExpr (encodeStateOperationsExpr slice)
with "((x / 2) % 36)" using eqString else ppStrings in

()
