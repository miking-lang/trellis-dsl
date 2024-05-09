-- Performs propagation of constraints relating a component of the from-state
-- to a component of the to-state (EqYPlusNum), by adding inequality
-- constraints on the to-state component. For instance, if we have a constraint
--
--   x[2] = y[2] - 1
--
-- we know y[2] = 0 is invalid, because it results in x[2] = -1, which is
-- outside the range of that component (we assume all ranges are normalized
-- to lower bound zero). The propagation defined in this file adds inequality
-- constraints (y[2] != 0 in the above example) such that all constraints on
-- the components of the to-state are stored in the set of the corresponding
-- component, rather than implicitly in a constraint on a from-state component.
--
-- In addition, we propagate any equality or inequality constraints on a
-- from-state components to any components of the to-state which are related
-- via a constraint.
--
-- This propagation opens up for two important optimizations in the compiler.
-- First, it enables us to immediately rule out invalid to-state values in the
-- "outer" conditional, rather than having to generate components of the
-- from-state (predecessor state) to rule it out. Second, it enables easily
-- determining whether a selection of sets of constraints covers all possible
-- to-states - this may allow us to combine conditional code for multiple
-- cases (very important for performance in CUDA), and also to compute a more
-- accurate upper bound on the maximum number of predecessors.

include "map.mc"
include "seq.mc"
include "set.mc"
include "utest.mc"

include "compile.mc"

lang TrellisConstraintPropagation = TrellisModelCompileSetConstraint
  -- Propagates constraints relating a component of the from-state with a
  -- component of the to-state, by adding new inequality constraints to the
  -- to-state.
  sem propagateConstraints : ConstraintRepr -> ConstraintRepr
  sem propagateConstraints =
  | constraints ->
    mapFoldWithKey
      (lam acc. lam. lam v. propagateRelativeConstraintsComponent acc v)
      constraints constraints.x

  sem propagateRelativeConstraintsComponent
    : ConstraintRepr -> Set PredConstraint -> ConstraintRepr
  sem propagateRelativeConstraintsComponent acc =
  | fromStateConstraints ->
    -- NOTE(larshum, 2024-05-09): If the from-state component has literal
    -- constraints, we propagate these to the relative constraints on
    -- components of the to-state.
    let litc = findLiteralConstraints fromStateConstraints in
    let acc =
      mapFoldWithKey
        (lam acc. lam k. lam.
          propagateLiteralConstraints litc acc k)
        acc fromStateConstraints
    in
    -- NOTE(larshum, 2024-05-09): Propagate inequality constraints that arise
    -- due to relative constraints and the value bounds of components to the
    -- related component of the to-state.
    mapFoldWithKey
      (lam acc. lam k. lam.
        propagateRelativeInequalityConstraints acc.state acc k)
      acc fromStateConstraints

  sem findLiteralConstraints : Set PredConstraint -> Set PredConstraint
  sem findLiteralConstraints =
  | constraints ->
    let getLiteralConstraint = lam c.
      match c with EqNum _ | NeqNum _ then true
      else false
    in
    mapFilterWithKey (lam c. lam. getLiteralConstraint c) constraints

  sem propagateLiteralConstraints
    : Set PredConstraint -> ConstraintRepr -> PredConstraint -> ConstraintRepr
  sem propagateLiteralConstraints literalConstraints acc =
  | EqYPlusNum (yidx, n, info) ->
    let addLiteralToStateConstraint = lam acc. lam c.
      match c with EqNum (en, _) then
        setInsert (EqNum (subi en n, info)) acc
      else match c with NeqNum (nn, _) then
        setInsert (NeqNum (subi nn n, info)) acc
      else acc
    in
    let c =
      setFold addLiteralToStateConstraint
        (setEmpty cmpPredConstraint) literalConstraints
    in
    if setIsEmpty c then acc
    else {acc with y = mapInsertWith setUnion yidx c acc.y}
  | _ -> acc

  sem propagateRelativeInequalityConstraints
    : [Int] -> ConstraintRepr -> PredConstraint -> ConstraintRepr
  sem propagateRelativeInequalityConstraints state acc =
  | EqYPlusNum (yidx, n, info) ->
    let upperBound = get state yidx in
    let invalidValues =
      if lti n 0 then create n (lam i. i)
      else create n (lam i. subi (subi upperBound i) 1)
    in
    let ineqConstraints = map (lam n. NeqNum (n, info)) invalidValues in
    let c = setOfSeq cmpPredConstraint ineqConstraints in
    if setIsEmpty c then acc
    else {acc with y = mapInsertWith setUnion yidx c acc.y}
  | _ -> acc
end

lang TestLang = TrellisConstraintPropagation + ConstraintTestLang
end

mexpr

use TestLang in

let printConstraints = lam l. lam r.
  let pp = printConstraintRepr in
  utestDefaultToString pp pp l r
in
let pc = setOfSeq cmpPredConstraint in

let eqn_ = lam n. EqNum (n, NoInfo ()) in
let neqn_ = lam n. NeqNum (n, NoInfo ()) in
let eqypn_ = lam yidx. lam n. EqYPlusNum (yidx, n, NoInfo ()) in

let int_ = lam n. TInt {bounds = Some (0, subi n 1), info = NoInfo ()} in
let ty = TTuple {tys = [int_ 4, int_ 4, int_ 4, int_ 16], info = NoInfo ()} in
let empty = defaultConstraintRepr (NoInfo ()) ty in
utest propagateConstraints empty with empty using eqConstraints else printConstraints in

let valid = {empty with x = mapFromSeq subi [(0, pc [eqn_ 1])]} in
utest propagateConstraints valid with valid using eqConstraints else printConstraints in

let yconstr1 = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 0])]
} in
utest propagateConstraints yconstr1 with yconstr1 using eqConstraints else printConstraints in

let yconstr2 = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 1])]
} in
let expected = {
  yconstr2 with y = mapFromSeq subi [(0, pc [neqn_ 3])]
} in
utest propagateConstraints yconstr2 with expected using eqConstraints else printConstraints in

let yconstr3 = {
  empty with x = mapFromSeq subi [(0, pc [eqn_ 1, eqypn_ 0 1])]
} in
let expected = {
  yconstr3 with y = mapFromSeq subi [(0, pc [eqn_ 0, neqn_ 3])]
} in
utest propagateConstraints yconstr3 with expected using eqConstraints else printConstraints in

let yconstr4 = {
  empty with x = mapFromSeq subi [(0, pc [neqn_ 2, eqypn_ 0 1])]
} in
let expected = {
  yconstr4 with y = mapFromSeq subi [(0, pc [neqn_ 1, neqn_ 3])]
} in
utest propagateConstraints yconstr4 with expected using eqConstraints else printConstraints in

()
