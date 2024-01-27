include "mexpr/info.mc"

include "ast.mc"
include "pprint.mc"

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

lang TrellisEncodeBitwise = TrellisEncodeBase + TrellisTypeBitwidth
  syn BOp =
  | OBitAnd ()
  | OSrl ()

  sem pprintBinOp =
  | OBitAnd _ -> "&"
  | OSrl _ -> ">>"

  sem generateBitwiseOperations : Info -> [TType] -> Int -> Int -> TExpr -> TExpr
  sem generateBitwiseOperations info tys lo hi =
  | target ->
    let bitwidths = map bitwidthType tys in
    let shift = foldl addi 0 (subsequence bitwidths (addi hi 1) (length tys)) in
    let sliceBitwidths = subsequence bitwidths lo (addi (subi hi lo) 1) in
    let mask = subi (slli 1 (foldl addi 0 sliceBitwidths)) 1 in
    let totBitwidth = foldl1 addi bitwidths in
    let resultTy = TInt {bounds = Some (0, totBitwidth), info = info} in
    applyBitmask info resultTy mask
      (applyRightShift info resultTy shift target)

  sem applyBitmask : Info -> TType -> Int -> TExpr -> TExpr
  sem applyBitmask info ty bitmask =
  | e ->
    let rhs = EInt {i = bitmask, ty = ty, info = info} in
    EBinOp {op = OBitAnd (), lhs = e, rhs = rhs, ty = ty, info = info}

  sem applyRightShift : Info -> TType -> Int -> TExpr -> TExpr
  sem applyRightShift info ty shiftAmount =
  | e ->
    if eqi shiftAmount 0 then e else
    let e = withTyTExpr ty e in
    let rhs = EInt {i = shiftAmount, ty = ty, info = info} in
    EBinOp {op = OSrl (), lhs = e, rhs = rhs, ty = ty, info = info}
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

lang TrellisEncodeExpr = TrellisEncodeBitwise + TrellisEncodeMixedRadix
  sem encodeStateOperationsExpr : Bool -> TExpr -> TExpr
  sem encodeStateOperationsExpr useBitset =
  | EVar t ->
    match t.ty with TTable _ then EVar t
    else
      let maxsz =
        if useBitset then slli 1 (bitwidthType t.ty)
        else cardinalityType t.ty
      in
      let ty = TInt {bounds = Some (0, maxsz), info = t.info} in
      EVar {t with ty = ty}
  | ESlice {target = target, lo = lo, hi = hi, ty = ty, info = info} ->
    if lti hi lo then errorSingle [info] "Invalid slice node" else
    let targetTy = tyTExpr target in
    let target = encodeStateOperationsExpr useBitset target in
    match targetTy with TTuple {tys = tys} then
      if useBitset then generateBitwiseOperations info tys lo hi target
      else generateMixedRadixOperations info tys lo hi target
    else errorSingle [info] "Projection has invalid type"
  | EBinOp (t & {op = OEq _ | ONeq _ | OLt _ | OGt _ | OLeq _ | OGeq _}) ->
    -- NOTE(larshum, 2024-01-25): When we compare a bit-encoded value with an
    -- integer literal, we add an offset based on the lower-bound of the
    -- encoded integer value. We have to do this because integers in a range
    -- a..b are encoded as values in the range 0..(b-a).
    let addOffset = lam ofs. lam e.
      if eqi ofs 0 then e else
      let intTy = tyTExpr e in
      let ofs = EInt {i = ofs, ty = intTy, info = t.info} in
      EBinOp {op = OAdd (), lhs = e, rhs = ofs, ty = intTy, info = t.info}
    in
    let lty = tyTExpr t.lhs in
    let rty = tyTExpr t.rhs in
    let lhs = encodeStateOperationsExpr useBitset t.lhs in
    let rhs = encodeStateOperationsExpr useBitset t.rhs in
    switch (lty, rty)
    case (TInt {bounds = Some (ofs, _)}, TInt {bounds = None _}) then
      EBinOp {t with lhs = addOffset ofs lhs, rhs = rhs, ty = lty}
    case (TInt {bounds = None _}, TInt {bounds = Some (ofs, _)}) then
      EBinOp {t with lhs = lhs, rhs = addOffset ofs rhs, ty = rty}
    case _ then
      EBinOp {t with lhs = lhs, rhs = rhs}
    end
  | e -> smapTExprTExpr (encodeStateOperationsExpr useBitset) e
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
    let encExpr = encodeStateOperationsExpr options.useBitsetEncoding in
    { cond = smapTSetTExpr encExpr cond
    , body = encExpr body }
end

lang TestLang = TrellisEncode + TrellisModelPrettyPrint
end

mexpr

use TestLang in

let pprintExpr = lam e.
  match pprintTrellisExpr pprintEnvEmpty e with (_, s) in s
in
let ppStrings = lam l. lam r.
  join ["    LHS: ", l, "\n    RHS: ", r]
in

utest findBitwidth 0 with 0 in
utest findBitwidth 1 with 1 in
utest findBitwidth 2 with 1 in
utest findBitwidth 3 with 2 in
utest findBitwidth 12 with 4 in
utest findBitwidth 16 with 4 in
utest findBitwidth 100 with 7 in

let i = infoVal "trellis-encode" 0 0 0 0 in
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

utest pprintExpr (encodeStateOperationsExpr false (proj 0))
with "((x / 12) % 6)" using eqString else ppStrings in
utest pprintExpr (encodeStateOperationsExpr false (proj 1))
with "((x / 2) % 6)" using eqString else ppStrings in
utest pprintExpr (encodeStateOperationsExpr false (proj 2))
with "(x % 2)" using eqString else ppStrings in

utest pprintExpr (encodeStateOperationsExpr true (proj 0))
with "((x >> 4) & 7)" using eqString else ppStrings in
utest pprintExpr (encodeStateOperationsExpr true (proj 1))
with "((x >> 1) & 7)" using eqString else ppStrings in
utest pprintExpr (encodeStateOperationsExpr true (proj 2))
with "(x & 1)" using eqString else ppStrings in

let slice = ESlice {
  target = x, lo = 0, hi = 1, ty = TTuple {tys = [ty2, ty2], info = i}, info = i
} in
utest pprintExpr (encodeStateOperationsExpr false slice)
with "((x / 2) % 36)" using eqString else ppStrings in
utest pprintExpr (encodeStateOperationsExpr true slice)
with "((x >> 1) & 63)" using eqString else ppStrings in

()
