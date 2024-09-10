-- Defines a conversion from the set constraint representation used in
-- predecessors.mc to a z3 file, and uses the z3 executable to check whether
-- this is satisfiable.

include "result.mc"
include "sys.mc"

include "repr.mc"
include "../z3.mc"

lang TrellisConstraintToZ3 = TrellisSetConstraintRepr + TrellisZ3Ast
  -- Declares the components of each component of a state and asserts the
  -- bounds on its value based on the size of each component.
  sem z3ImplicitConstraints : [Int] -> String -> Z3Program
  sem z3ImplicitConstraints stateBounds =
  | prefix ->
    let n = length stateBounds in
    let var = lam i. concat prefix (int2string i) in

    -- Declare the state components as constants in Z3.
    let declConst = lam i. ZDConst {id = var i, ty = ZTInt ()} in

    -- Add assertions based on the bounds of each component based on the type.
    let lowerBoundAssert = lam i.
      ZDAssert {e = ZEBinOp {
        op = ZBGe (), lhs = ZEVar {id = var i}, rhs = ZEInt {i = 0} }}
    in
    let upperBoundAssert = lam i.
      let ub = get stateBounds i in
      ZDAssert {e = ZEBinOp {
        op = ZBLt (), lhs = ZEVar {id = var i}, rhs = ZEInt {i = ub} }}
    in
    let boundAsserts = lam i.
      [lowerBoundAssert i, upperBoundAssert i]
    in
    join [create n declConst, join (create n boundAsserts)]

  -- Produces a sequence of Z3 expressions representing the given predecessor
  -- constraints.
  sem z3ComponentConstraints : Map Int (Set PredConstraint) -> String -> [Z3Expr]
  sem z3ComponentConstraints compConstraints =
  | prefix ->
    let toZ3Constraint = lam i. lam c.
      let var = ZEVar {id = concat prefix (int2string i)} in
      map (constraintToZ3Expression var) (setToSeq c)
    in
    join (mapValues (mapMapWithKey toZ3Constraint compConstraints))

  sem constraintToZ3Expression : Z3Expr -> PredConstraint -> Z3Expr
  sem constraintToZ3Expression lhs =
  | EqNum (n, _) ->
    ZEBinOp {op = ZBEq (), lhs = lhs, rhs = ZEInt {i = n}}
  | NeqNum (n, _) ->
    ZEUnOp {
      op = ZUNot (),
      target = ZEBinOp {op = ZBEq (), lhs = lhs, rhs = ZEInt {i = n}}}
  | EqYPlusNum (yidx, n, _) ->
    let rhsVar = ZEVar {id = concat "y" (int2string yidx)} in
    ZEBinOp {
      op = ZBEq (), lhs = lhs,
      rhs = ZEBinOp {op = ZBAdd (), lhs = rhsVar, rhs = ZEInt {i = n}}}

  sem z3And : Z3Expr -> Z3Expr -> Z3Expr
  sem z3And lhs =
  | rhs -> ZEBinOp {op = ZBAnd (), lhs = lhs, rhs = rhs}

  -- Converts the given set constraint to a satisfiability problem in Z3,
  -- which is satisfiable when the constraint is non-empty.
  sem z3NonEmptyProblem : ConstraintRepr -> Z3Program
  sem z3NonEmptyProblem =
  | {state = state, x = x, y = y} ->
    -- Declare the state component types and introduce their implicit
    -- constraints based on their types.
    let x1 = z3ImplicitConstraints state "x" in
    let y1 = z3ImplicitConstraints state "y" in

    -- Convert the explicit constraints to an Z3 assertion that the conjunction
    -- of these formulas hold.
    let x2 = z3ComponentConstraints x "x" in
    let y2 = z3ComponentConstraints y "y" in
    let c = concat x2 y2 in
    let assertExpr =
      if null c then ZETrue ()
      else foldl1 z3And c
    in
    let assertion = ZDAssert {e = assertExpr} in
    join [x1, y1, [assertion, ZDCheckSat ()]]

  -- Converts the given set constraints to a satisfiability problem in Z3,
  -- which is satisfiable when there exists a target state not included in any
  -- of the given set constraint representations.
  sem z3DoesNotCoverAllTargetStatesProblem : [ConstraintRepr] -> Z3Program
  sem z3DoesNotCoverAllTargetStatesProblem =
  | ([{state = state}] ++ _) & constraintsSeq ->
    let base = z3ImplicitConstraints state "y" in

    -- Convert the explicit constraints on the target state components of each
    -- constraint instance to a Z3 program.
    let c = map (lam c. z3ComponentConstraints c.y "y") constraintsSeq in

    -- Assert that none of the constraint instances hold, and attempt to find a
    -- target state for which this is true. If Z3 can find such a target state,
    -- we know the given constraints do not cover all target states.
    let asserts =
      map
        (lam x.
          -- If a constraint representation has no constraints, this means it
          -- includes all to states. In this case, we know there can be no such
          -- state, so we assert false.
          let assertExpr =
            if null x then ZEFalse ()
            else ZEUnOp {op = ZUNot (), target = foldl1 z3And x}
          in
          ZDAssert {e = assertExpr})
        c
    in
    join [base, asserts, [ZDCheckSat ()]]
end

lang TrellisConstraintZ3 = TrellisConstraintToZ3 + TrellisZ3Run

  -- Checks whether the provided constraint representation describing a set of
  -- transitions between pairs of states is empty. We do this by having Z3 find
  -- a satisfying solution to the provided constraints - if there is such a
  -- solution, the set is non-empty.
  sem checkEmpty : ConstraintRepr -> Result () Z3Error Bool
  sem checkEmpty =
  | constraints ->
    result.map not (runZ3SatProgram (z3NonEmptyProblem constraints))

  -- Verifies that the given constraints cover all possible values of
  -- target states.
  sem checkCoversAllTargetStates : [ConstraintRepr] -> Result () Z3Error Bool
  sem checkCoversAllTargetStates =
  | constraints ->
    result.map not (runZ3SatProgram (z3DoesNotCoverAllTargetStatesProblem constraints))
end

mexpr

use TrellisConstraintZ3 in

-- NOTE(larshum, 2024-04-24): Skip running the tests in this file if z3 is not
-- installed.
if not (checkZ3Installed ()) then () else

let eqn_ = lam n. EqNum (n, NoInfo ()) in
let neqn_ = lam n. NeqNum (n, NoInfo ()) in
let eqypn_ = lam yidx. lam n. EqYPlusNum (yidx, n, NoInfo ()) in

let eqCheck = lam l. lam r.
  switch (result.consume l, result.consume r)
  case ((_, Right lv), (_, Right rv)) then eqBool lv rv
  case ((_, Left le), (_, Left re)) then eqSeq eqZ3Error le re
  case _ then false
  end
in

-- Tests for the empty check
let pc = setOfSeq cmpPredConstraint in
let empty = {
  state = [4, 4, 4, 16],
  x = mapEmpty subi, y = mapEmpty subi, info = NoInfo ()
} in
utest checkEmpty empty with result.ok false using eqCheck in

let x = mapFromSeq subi [
  (0, pc [eqypn_ 0 0]),
  (1, pc [eqypn_ 1 0]),
  (2, pc [eqypn_ 2 0]),
  (3, pc [eqn_ 15])
] in
let y = mapFromSeq subi [
  (3, pc [eqn_ 14])
] in
let lhs = {
  empty with x = x, y = y
} in
utest checkEmpty lhs with result.ok false using eqCheck in

let x = mapFromSeq subi [
  (0, pc [eqypn_ 0 0]),
  (1, pc [eqypn_ 1 0]),
  (2, pc [eqypn_ 2 0]),
  (3, pc [eqypn_ 3 1])
] in
let y = mapFromSeq subi [
  (3, pc [neqn_ 15])
] in
let rhs1 = {
  empty with x = x, y = y
} in
utest checkEmpty rhs1 with result.ok false using eqCheck in

let y = mapFromSeq subi [
  (3, pc [neqn_ 15, neqn_ 14])
] in
let rhs2 = {
  empty with x = x, y = y
} in
utest checkEmpty rhs2 with result.ok false using eqCheck in

let q1 = {lhs with
  x = mapUnionWith setUnion lhs.x rhs1.x,
  y = mapUnionWith setUnion lhs.y rhs1.y
} in
utest checkEmpty q1 with result.ok false using eqCheck in

let q2 = {lhs with
  x = mapUnionWith setUnion lhs.x rhs2.x,
  y = mapUnionWith setUnion lhs.y rhs2.y
} in
utest checkEmpty q2 with result.ok true using eqCheck in

-- Below are contradictory examples that are considered empty as no valid pairs
-- of states can be contained in them.
let q3 = {
  empty with x = mapFromSeq subi [(0, pc [eqn_ 0, eqn_ 1])]
} in
utest checkEmpty q3 with result.ok true using eqCheck in

let q4 = {
  empty with x = mapFromSeq subi [(0, pc [neqn_ 0, neqn_ 1, neqn_ 2, neqn_ 3])]
} in
utest checkEmpty q4 with result.ok true using eqCheck in

let q5 = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 3])],
             y = mapFromSeq subi [(0, pc [neqn_ 0])]
} in
utest checkEmpty q5 with result.ok true using eqCheck in

let q6 = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 0, eqn_ 0])],
             y = mapFromSeq subi [(0, pc [eqn_ 1])]
} in
utest checkEmpty q6 with result.ok true using eqCheck in

let q7 = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 0, eqypn_ 1 1])],
             y = mapFromSeq subi [(0, pc [eqn_ 2]), (1, pc [neqn_ 1])]
} in
utest checkEmpty q7 with result.ok true using eqCheck in

let q8 = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 3]), (1, pc [eqypn_ 0 0, eqypn_ 1 0])],
             y = mapFromSeq subi [(1, pc [neqn_ 0])]
} in
utest checkEmpty q8 with result.ok true using eqCheck in

-- Tests for the to-state completeness check
utest checkCoversAllTargetStates [q3] with result.ok true using eqCheck in
utest checkCoversAllTargetStates [q4] with result.ok true using eqCheck in
utest checkCoversAllTargetStates [q3, q4] with result.ok true using eqCheck in
utest checkCoversAllTargetStates [q5] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [q4, q5] with result.ok true using eqCheck in
utest checkCoversAllTargetStates [q6] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [q5, q6] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [q5, q6, q8] with result.ok false using eqCheck in

let a = {
  empty with y = mapFromSeq subi [(3, pc [eqn_ 15])]
} in
let b = {
  empty with y = mapFromSeq subi [(3, pc [eqn_ 14])]
} in
let c = {
  empty with y = mapFromSeq subi [(3, pc [neqn_ 14, neqn_ 15])]
} in
utest checkCoversAllTargetStates [a] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [b] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [c] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [a, b] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [a, c] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [b, c] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [a, b, c] with result.ok true using eqCheck in

let a = {
  empty with y = mapFromSeq subi [(0, pc [eqn_ 0])]
} in
let b = {
  empty with y = mapFromSeq subi [(0, pc [neqn_ 0]), (1, pc [neqn_ 3])]
} in
let c = {
  empty with y = mapFromSeq subi [(0, pc [neqn_ 0]), (1, pc [eqn_ 3])]
} in
utest checkCoversAllTargetStates [a] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [b] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [c] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [a, b] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [a, c] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [b, c] with result.ok false using eqCheck in
utest checkCoversAllTargetStates [a, b, c] with result.ok true using eqCheck in

()
