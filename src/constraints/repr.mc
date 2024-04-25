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
    infos : [Info]
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
    { state = state, x = mapEmpty subi, y = mapEmpty subi, infos = [info] }

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
end
