-- Compiles a set constraint in the Trellis model AST representation to an
-- abstract constraint representation.

include "result.mc"
include "utest.mc"
include "mexpr/info.mc"

include "../model/ast.mc"
include "../model/eq.mc"
include "repr.mc"

lang TrellisModelCompileSetConstraintError
  -- An error type representing the reason why the translation from the Trellis
  -- model AST to the abstract representation failed.
  syn ConstraintError =
  | UnsupportedSet Info
  | UnsupportedCondition Info
  | UnsupportedEquality Info

  sem printSection : Bool -> [Info] -> String -> String
  sem printSection warning infos =
  | msg ->
    let section = {errorDefault with msg = msg, infos = infos} in
    match errorMsg [section] {single = "", multi = ""} with (i, msg) in
    if warning then infoWarningString i msg
    else infoErrorString i msg

  sem printConstraintErrorMessage : Bool -> ConstraintError -> String
  sem printConstraintErrorMessage warning =
  | UnsupportedSet i ->
    printSection warning [i] "Unsupported set construct"
  | UnsupportedCondition i ->
    printSection warning [i] "Unsupported condition expression"
  | UnsupportedEquality i ->
    printSection warning [i] "Unsupported shape of equality/inequality condition"

  sem eqConstraintError : ConstraintError -> ConstraintError -> Bool
  sem eqConstraintError l =
  | r ->
    if eqi (constructorTag l) (constructorTag r) then
      eqConstraintErrorH (l, r)
    else false

  sem eqConstraintErrorH : (ConstraintError, ConstraintError) -> Bool
  sem eqConstraintErrorH =
  | (UnsupportedSet li, UnsupportedSet ri) -> eqi (infoCmp li ri) 0
  | (UnsupportedCondition li, UnsupportedCondition ri) ->
    eqi (infoCmp li ri) 0
  | (UnsupportedEquality li, UnsupportedEquality ri) ->
    eqi (infoCmp li ri) 0
end

lang TrellisModelCompileSetConstraint =
  TrellisModelCompileSetConstraintError + TrellisModelAst +
  TrellisSetConstraintRepr

  type ConstraintResult = Result () ConstraintError ConstraintRepr

  -- Converts a transition set constraint with a given state type to the
  -- abstract constraint representation. If the set constraint is a value
  -- builder, or the conditional expressions contain unsupported expressions,
  -- all errors are returned instead.
  sem setConstraintToRepr : TType -> TSet -> ConstraintResult
  sem setConstraintToRepr stateType =
  | SAll t ->
    -- NOTE(larshum, 2024-04-24): The default constraint representation
    -- contains no constraints on either state, which corresponds to a set
    -- containing transitions between all pairs of states.
    result.ok (defaultConstraintRepr t.info stateType)
  | SValueBuilder t ->
    result.err (UnsupportedSet t.info)
  | STransitionBuilder t ->
    let acc = result.ok (defaultConstraintRepr t.info stateType) in
    foldl
      (lam acc. lam cond. extractCondition t.x t.y acc cond)
      acc t.conds

  sem extractCondition : Name -> Name -> ConstraintResult -> TExpr
                      -> ConstraintResult
  sem extractCondition x y acc =
  | EBinOp {
      op = op & (OEq _ | ONeq _),
      lhs = ESlice {target = EVar {id = id}, lo = lo, hi = hi},
      rhs = EInt {i = i},
      info = info
    }
  | EBinOp {
      op = op & (OEq _ | ONeq _),
      lhs = EInt {i = i},
      rhs = ESlice {target = EVar {id = id}, lo = lo, hi = hi},
      info = info
    } ->
    if eqi lo hi then
      let idx = lo in
      let value =
        match op with OEq _ then EqNum (i, info)
        else NeqNum (i, info)
      in
      let c = singletonConstraint value in
      if nameEq id x then
        result.map (lam env. {env with x = mapInsertWith setUnion idx c env.x}) acc
      else if nameEq id y then
        result.map (lam env. {env with y = mapInsertWith setUnion idx c env.y}) acc
      else
        result.withAnnotations acc (result.err (UnsupportedEquality info))
    else error "Predecessor analysis expected individual components, not slices"
  | EBinOp {
      op = OEq (),
      lhs = ESlice {target = EVar {id = id1}, lo = lo1, hi = hi1},
      rhs = ESlice {target = EVar {id = id2}, lo = lo2, hi = hi2},
      info = info
    } ->
    if and (eqi lo1 hi1) (eqi lo2 hi2) then
      match
        if and (nameEq id1 x) (nameEq id2 y) then Some (lo1, lo2)
        else if and (nameEq id2 x) (nameEq id1 y) then Some (lo2, lo1)
        else None ()
      with Some (xidx, yidx) then
        let c = singletonConstraint (EqYPlusNum (yidx, 0, info)) in
        result.map (lam env. {env with x = mapInsertWith setUnion xidx c env.x}) acc
      else
        result.withAnnotations acc (result.err (UnsupportedEquality info))
    else error "Predecessor analysis expected individual components, not slices"
  | EBinOp {
      op = OEq (),
      lhs = ESlice {target = EVar {id = id1}, lo = lo1, hi = hi1, ty = ty},
      rhs = EBinOp {
        op = OAdd (),
        lhs = ESlice {target = EVar {id = id2}, lo = lo2, hi = hi2},
        rhs = EInt {i = n}},
      info = info
    }
  | EBinOp {
      op = OEq (),
      lhs = EBinOp {
        op = OAdd (),
        lhs = ESlice {target = EVar {id = id2}, lo = lo2, hi = hi2},
        rhs = EInt {i = n}},
      rhs = ESlice {target = EVar {id = id1}, lo = lo1, hi = hi1, ty = ty},
      info = info
    } ->
    if and (eqi lo1 hi1) (eqi lo2 hi2) then
      match
        if and (nameEq id1 x) (nameEq id2 y) then Some (lo1, lo2, n)
        else if and (nameEq id2 x) (nameEq id1 y) then Some (lo2, lo1, negi n)
        else None ()
      with Some (xidx, yidx, n) then
        let c = singletonConstraint (EqYPlusNum (yidx, n, info)) in
        result.map (lam env. {env with x = mapInsertWith setUnion xidx c env.x}) acc
      else
        result.withAnnotations acc (result.err (UnsupportedEquality info))
    else
      error "Predecessor analysis expected individual components, not slices"
  | EBinOp {op = OEq _ | ONeq _, info = info} ->
    result.withAnnotations acc (result.err (UnsupportedEquality info))
  | e ->
    result.withAnnotations acc (result.err (UnsupportedCondition (infoTExpr e)))
end

lang ConstraintTestLang =
  TrellisModelCompileSetConstraint + TrellisModelTypeEq

  sem eqConstraints : ConstraintRepr -> ConstraintRepr -> Bool
  sem eqConstraints l =
  | r ->
    if forAll (lam x. eqi x.0 x.1) (zip l.state r.state) then
      if mapEq setEq l.x r.x then mapEq setEq l.y r.y
      else false
    else false

  sem eqc : ConstraintResult -> ConstraintResult -> Bool
  sem eqc l =
  | r -> eqcH (result.consume l, result.consume r)

  type T = ([()], Either [ConstraintError] ConstraintRepr)

  sem eqcH : (T, T) -> Bool
  sem eqcH =
  | ((_, Right l), (_, Right r)) -> eqConstraints l r
  | ((_, Left l), (_, Left r)) -> eqSeq eqConstraintError l r
  | _ -> false

  sem ppc : ConstraintResult -> ConstraintResult -> String
  sem ppc l =
  | r ->
    let pp = lam r.
      let x = result.consume r in
      match x with (_, Right c) then printConstraintRepr c
      else match x with (_, Left errs) then
        strJoin "\n" (map (printConstraintErrorMessage true) errs)
      else never
    in
    utestDefaultToString pp pp l r
end

mexpr

use ConstraintTestLang in

-- NOTE(larshum, 2024-04-24): The constraint analysis does not consider the
-- type information, so we use an integer type with lower and upper bound zero
-- to indicate absent type information.
let intTy_ = lam n. TInt { bounds = Some (0, subi n 1), info = NoInfo () } in
let int_ = lam n.
  EInt {i = n, ty = intTy_ 0, info = NoInfo ()}
in
let var_ = lam id.
  EVar {id = id, ty = intTy_ 0, info = NoInfo ()}
in
let slice_ = lam id. lam idx.
  ESlice {target = var_ id, lo = idx, hi = idx, ty = intTy_ 0, info = NoInfo ()}
in
let bop_ = lam op. lam l. lam r.
  EBinOp {op = op, lhs = l, rhs = r, ty = intTy_ 0, info = NoInfo ()}
in
let add_ = bop_ (OAdd ()) in
let eq_ = bop_ (OEq ()) in
let neq_ = bop_ (ONeq ()) in

let eqn_ = lam n. EqNum (n, NoInfo ()) in
let neqn_ = lam n. NeqNum (n, NoInfo ()) in
let eqypn_ = lam yidx. lam n. EqYPlusNum (yidx, n, NoInfo ()) in

let cset = lam c. setOfSeq cmpPredConstraint c in
let tys = [intTy_ 4, intTy_ 4, intTy_ 4, intTy_ 16] in
let stateTy = TTuple {tys = tys, info = NoInfo ()} in
let empty = defaultConstraintRepr (NoInfo ()) stateTy in

let x = nameSym "x" in
let y = nameSym "y" in

-- Conversion of condition expressions
let extTest = extractCondition x y (result.ok empty) in
let e1 = eq_ (slice_ x 0) (int_ 0) in
let expected = {
  empty with x = mapFromSeq subi [(0, cset [eqn_ 0])]
} in
utest extTest e1 with result.ok expected using eqc else ppc in

let e2 = eq_ (slice_ x 0) (slice_ y 0) in
let expected = {
  empty with x = mapFromSeq subi [(0, cset [eqypn_ 0 0])]
} in
utest extTest e2 with result.ok expected using eqc else ppc in

let e3 = eq_ (slice_ x 0) (add_ (slice_ y 0) (int_ 1)) in
let expected = {
  empty with x = mapFromSeq subi [(0, cset [eqypn_ 0 1])]
} in
utest extTest e3 with result.ok expected using eqc else ppc in

let e4 = eq_ (slice_ y 0) (int_ 1) in
let expected = {
  empty with y = mapFromSeq subi [(0, cset [eqn_ 1])]
} in
utest extTest e4 with result.ok expected using eqc else ppc in

let e5 = neq_ (slice_ x 0) (int_ 0) in
let expected = {
  empty with x = mapFromSeq subi [(0, cset [neqn_ 0])]
} in
utest extTest e5 with result.ok expected using eqc else ppc in

let e6 = neq_ (slice_ y 1) (int_ 2) in
let expected = {
  empty with y = mapFromSeq subi [(1, cset [neqn_ 2])]
} in
utest extTest e6 with result.ok expected using eqc else ppc in

let e7 = eq_ (slice_ x 0) (slice_ x 1) in
let e8 = neq_ (slice_ x 0) (slice_ y 0) in
let e9 = eq_ (slice_ y 0) (slice_ y 1) in
let unsuppEq = result.err (UnsupportedEquality (NoInfo ())) in
utest extTest e7 with unsuppEq using eqc else ppc in
utest extTest e8 with unsuppEq using eqc else ppc in
utest extTest e9 with unsuppEq using eqc else ppc in

let e10 = bop_ (OLt ()) (slice_ x 0) (slice_ y 0) in
let unsuppCond = result.err (UnsupportedCondition (NoInfo ())) in
utest extTest e10 with unsuppCond using eqc else ppc in

let e11 = eq_ (slice_ y 3) (add_ (slice_ x 3) (int_ -1)) in
let expected = {
  empty with x = mapFromSeq subi [(3, cset [eqypn_ 3 1])]
} in
utest extTest e11 with result.ok expected using eqc else ppc in

-- Conversion of sets
let s1 = SAll {info = NoInfo ()} in
utest setConstraintToRepr stateTy s1 with result.ok empty using eqc else ppc in

let s2 = SValueBuilder {x = x, info = NoInfo (), conds = [], info = NoInfo ()} in
let unsuppSet = result.err (UnsupportedSet (NoInfo ())) in
utest setConstraintToRepr stateTy s2 with unsuppSet using eqc else ppc in

let tbset = lam conds.
  STransitionBuilder {x = x, y = y, info = NoInfo (), conds = conds}
in
let s3 = tbset [ e1 ] in
let expected = {
  empty with x = mapFromSeq subi [(0, cset [eqn_ 0])]
} in
utest setConstraintToRepr stateTy s3 with result.ok expected using eqc else ppc in

let s4 = tbset [ e1, e2, e4 ] in
let expected = {
  empty with x = mapFromSeq subi [(0, cset [eqn_ 0, eqypn_ 0 0])],
             y = mapFromSeq subi [(0, cset [eqn_ 1])]
} in
utest setConstraintToRepr stateTy s4 with result.ok expected using eqc else ppc in

let s5 = tbset [ e1, e7, e5 ] in
utest setConstraintToRepr stateTy s5 with unsuppEq using eqc else ppc in

let s6 = tbset [ e7, e10 ] in
let expected = result.withAnnotations unsuppEq unsuppCond in
utest setConstraintToRepr stateTy s6 with expected using eqc else ppc in

()
