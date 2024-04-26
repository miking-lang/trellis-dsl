-- Defines the abstract representation of a set constraint.

include "map.mc"
include "set.mc"
include "string.mc"
include "mexpr/info.mc"

include "../model/ast.mc"
include "../model/encode.mc"

lang TrellisSetConstraintRepr = TrellisModelAst + TrellisTypeCardinality
  syn PredConstraint =
  | EqNum (Int, Info)
  | NeqNum (Int, Info)
  | EqYPlusNum (Int, Int, Info)

  sem printPredConstraint : PredConstraint -> String
  sem printPredConstraint =
  | EqNum (n, _) -> concat " == " (int2string n)
  | NeqNum (n, _) -> concat " != " (int2string n)
  | EqYPlusNum (idx, n, _) ->
    if eqi n 0 then join [" == y[", int2string idx, "]"]
    else join [" == y[", int2string idx, "] + ", int2string n]

  sem cmpPredConstraint : PredConstraint -> PredConstraint -> Int
  sem cmpPredConstraint l =
  | r ->
    let lc = constructorTag l in
    let rc = constructorTag r in
    if eqi lc rc then cmpPredConstraintH (l, r)
    else subi lc rc

  sem cmpPredConstraintH : (PredConstraint, PredConstraint) -> Int
  sem cmpPredConstraintH =
  | (EqNum (ln, _), EqNum (rn, _)) -> subi ln rn
  | (NeqNum (ln, _), NeqNum (rn, _)) -> subi ln rn
  | (EqYPlusNum (ly, ln, _), EqYPlusNum (ry, rn, _)) ->
    let c = subi ly ry in
    if eqi c 0 then subi ln rn else c

  sem singletonConstraint : PredConstraint -> Set PredConstraint
  sem singletonConstraint =
  | c -> setOfSeq cmpPredConstraint [c]

  type ConstraintRepr = {
    state : [Int],
    x : Map Int (Set PredConstraint),
    y : Map Int (Set PredConstraint),
    info : Info
  }

  sem defaultConstraintRepr : Info -> TType -> ConstraintRepr
  sem defaultConstraintRepr info =
  | stateType ->
    -- NOTE(larshum, 2024-04-24): We assume all components of the state type
    -- have been transformed to be values in the range [0, n), where n is the
    -- (excluded) upper bound, computed based on the cardinality of the type of
    -- each component of the complete type.
    let state =
      match stateType with TTuple {tys = tys} then map cardinalityType tys
      else [cardinalityType stateType]
    in
    { state = state, x = mapEmpty subi, y = mapEmpty subi, info = info }

  sem printConstraintRepr : ConstraintRepr -> String
  sem printConstraintRepr =
  | {state = _, x = x, y = y} ->
    let printConstraint = lam lhs. lam c.
      join [lhs, printPredConstraint c]
    in
    let printEntry = lam target. lam acc. lam idx. lam constraints.
      let lhs = join [target, "[", int2string idx, "]"] in
      concat acc (map (printConstraint lhs) (setToSeq constraints))
    in
    let acc = mapFoldWithKey (printEntry "x") [] x in
    strJoin ", " (mapFoldWithKey (printEntry "y") acc y)

  sem countPredecessors : ConstraintRepr -> Int
  sem countPredecessors =
  | {state = state, x = x} ->
    let isEqualityConstraint = lam c.
      match c with EqNum _ | EqYPlusNum _ then true else false
    in
    let countComponent = lam i. lam n.
      match mapLookup i x with Some componentConstraints then
        let s = setToSeq componentConstraints in
        -- NOTE(larshum, 2024-04-26): If the constraints include any equality
        -- with a literal or a component of the to-state, there is only one
        -- possible value for this component for a given to-state (we assume
        -- the constraints have already been validated). Otherwise, the number
        -- of possible values depends on how many inequality constraints we
        -- have (each reduces the number of possibilities by one).
        if any isEqualityConstraint s then 1
        else subi n (length s)
      else n
    in
    foldl muli 1 (mapi countComponent state)
end

mexpr

use TrellisSetConstraintRepr in

let toset = setOfSeq cmpPredConstraint in
let int_ = lam n. TInt {bounds = Some (0, subi n 1), info = NoInfo ()} in
let stateTy = TTuple {tys = [int_ 4, int_ 7, int_ 3, int_ 2], info = NoInfo ()} in
let c1 = defaultConstraintRepr (NoInfo ()) stateTy in
utest countPredecessors c1 with foldl muli 1 [4, 7, 3, 2] in

let c2 = {c1 with x = mapInsertWith setUnion 0 (toset [EqNum (0, NoInfo ())]) c1.x} in
utest countPredecessors c2 with foldl muli 1 [1, 7, 3, 2] in

let c3 = {c2 with x = mapInsertWith setUnion 1 (toset [NeqNum (4, NoInfo ())]) c2.x} in
utest countPredecessors c3 with foldl muli 1 [1, 6, 3, 2] in

let c4 = {c3 with x = mapInsertWith setUnion 2 (toset [EqYPlusNum (0, 0, NoInfo ())]) c3.x} in
utest countPredecessors c4 with foldl muli 1 [1, 6, 1, 2] in

-- If the constraints of one component prevent any valid values for that
-- component the total number of possible predecessors becomes zero as we
-- cannot instantiate that component.
let c5 = {c4 with
  x = mapInsertWith setUnion 3 (toset [NeqNum (0, NoInfo ()), NeqNum (1, NoInfo ())]) c4.x
} in
utest countPredecessors c5 with 0 in

()
