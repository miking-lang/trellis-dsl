-- Replaces operations on state and output variables with bitwise operations,
-- which are added to the model AST.

include "math.mc"
include "string.mc"

include "ast.mc"
include "cardinality.mc"
include "pprint.mc"

lang TrellisBitwiseBase = TrellisModelAst + TrellisModelPrettyPrint
  syn BOp =
  | OBitAnd ()
  | OSrl ()

  sem pprintBinOp =
  | OBitAnd _ -> "&"
  | OSrl _ -> ">>"
end

lang TrellisBitwiseType = TrellisBitwiseBase + TrellisTypeCardinality
  -- Finds the number of bits needed to represent a number up to the given
  -- integer value.
  sem findBitwidth : Int -> Int
  sem findBitwidth =
  | 0 -> 0
  | 1 -> 1
  | n ->
    recursive let work = lam count. lam i.
      if lti i n then work (addi count 1) (slli i 1)
      else count
    in work 0 1

  -- Computes the number of bits needed to represent all possible values of a
  -- given (finite) type.
  sem bitwidthType : TType -> Int
  sem bitwidthType =
  | TBool _ -> 1
  | TInt {bounds = Some (lb, ub)} -> findBitwidth (addi (subi ub lb) 1)
  | TInt {bounds = None _, info = info} | TProb {info = info} ->
    errorSingle [info] "Cannot compute bit width of infinite type"
  | TTuple {tys = tys} -> foldl1 addi (map bitwidthType tys)
  | TTable {info = info} ->
    errorSingle [info] "Cannot compute bit width of a table type"
end

lang TrellisBitwiseExpr = TrellisBitwiseType
  sem applyBitmask : Info -> Int -> Int -> TExpr -> TExpr
  sem applyBitmask info targetCardinality bitmask =
  | e ->
    let ty = TInt {bounds = Some (0, targetCardinality), info = info} in
    let rhs = EInt {i = bitmask, ty = ty, info = info} in
    EBinOp {op = OBitAnd (), lhs = e, rhs = rhs, ty = ty, info = info}

  sem applyRightShift : Info -> Int -> Int -> TExpr -> TExpr
  sem applyRightShift info targetCardinality shiftAmount =
  | e ->
    if eqi shiftAmount 0 then e else
    let ty = TInt {bounds = Some (0, targetCardinality), info = info} in
    let e = withTyTExpr ty e in
    let rhs = EInt {i = shiftAmount, ty = ty, info = info} in
    EBinOp {op = OSrl (), lhs = e, rhs = rhs, ty = ty, info = info}

  sem insertBitwiseOperations : TExpr -> TExpr
  sem insertBitwiseOperations =
  | EVar t ->
    match t.ty with TTable _ then EVar t
    else
      let maxsz = slli 1 (findBitwidth (typeCardinality t.ty)) in
      let ty = TInt {bounds = Some (0, maxsz), info = t.info} in
      EVar {t with ty = ty}
  | ESlice {target = target, lo = lo, hi = hi, ty = ty, info = info} ->
    if lti hi lo then errorSingle [info] "Invalid slice node" else
    let targetTy = tyTExpr target in
    let target = insertBitwiseOperations target in
    match targetTy with TTuple {tys = tys} then
      let bitwidths = map bitwidthType tys in
      let cardinality = typeCardinality targetTy in
      let shift = foldl addi 0 (subsequence bitwidths (addi hi 1) (length tys)) in
      let sliceBitwidths = subsequence bitwidths lo (addi (subi hi lo) 1) in
      let mask = subi (slli 1 (foldl addi 0 sliceBitwidths)) 1 in
      applyBitmask info cardinality mask
        (applyRightShift info cardinality shift target)
    else errorSingle [info] "Projection has invalid type"
  | EBinOp (t & { op = OEq _ | ONeq _ | OLt _ | OGt _ | OLeq _ | OGeq _ }) ->
    -- NOTE(larshum, 2024-01-25): When we compare a bit-encoded value with an
    -- integer literal, we add an offset based on the lower-bound of the
    -- encoded integer value. This is because integers in range a..b are
    -- bit-encoded as values in the range 0..(b-a).
    let addOffset = lam ofs. lam e.
      if eqi ofs 0 then e else
      let intTy = TInt {bounds = None (), info = t.info} in
      let ofs = EInt {i = ofs, ty = intTy, info = t.info} in
      EBinOp {op = OAdd (), lhs = e, rhs = ofs, ty = intTy, info = t.info}
    in
    let lty = tyTExpr t.lhs in
    let rty = tyTExpr t.rhs in
    let lhs = insertBitwiseOperations t.lhs in
    let rhs = insertBitwiseOperations t.rhs in
    switch (lty, rty)
    case (TInt {bounds = Some (ofs, _)}, TInt {bounds = None _}) then
      EBinOp {t with lhs = addOffset ofs lhs, rhs = rhs, ty = lty}
    case (TInt {bounds = None _}, TInt {bounds = Some (ofs, _)}) then
      EBinOp {t with lhs = lhs, rhs = addOffset ofs rhs, ty = rty}
    case _ then
      EBinOp {t with lhs = lhs, rhs = rhs}
    end
  | e -> smapTExprTExpr insertBitwiseOperations e
end

lang TrellisBitwise = TrellisBitwiseType + TrellisBitwiseExpr
end

lang TestLang = TrellisBitwise + TrellisModelPrettyPrint
end

mexpr

use TestLang in

let pprintExpr = lam e.
  match pprintTrellisExpr pprintEnvEmpty e with (_, s) in
  s
in

let ppStrings = lam l. lam r.
  join ["    LHS: ", l, "\n", "    RHS: ", r]
in

utest findBitwidth 2 with 1 in
utest findBitwidth 3 with 2 in
utest findBitwidth 12 with 4 in
utest findBitwidth 16 with 4 in
utest findBitwidth 100 with 7 in

let i = NoInfo () in
let ty1 = TBool {info = i} in
let ty2 = TInt {bounds = Some (3, 8), info = i} in
let ty3 = TTuple {tys = [ty2, ty2, ty1], info = i} in
utest bitwidthType ty1 with 1 in
utest bitwidthType ty2 with 3 in
utest bitwidthType ty3 with 7 in

let x = EVar {id = nameNoSym "x", ty = ty3, info = i} in
let proj = lam idx. ESlice {target = x, lo = idx, hi = idx, ty = ty2, info = i} in
utest pprintExpr (insertBitwiseOperations (proj 0)) with "((x >> 4) & 7)"
using eqString else ppStrings in
utest pprintExpr (insertBitwiseOperations (proj 1)) with "((x >> 1) & 7)"
using eqString else ppStrings in
utest pprintExpr (insertBitwiseOperations (proj 2)) with "(x & 1)"
using eqString else ppStrings in

let slice = ESlice {
  target = x, lo = 0, hi = 1, ty = TTuple {tys = [ty2, ty2], info = i}, info = i
} in
utest pprintExpr (insertBitwiseOperations slice) with "((x >> 1) & 63)"
using eqString else ppStrings in

()
