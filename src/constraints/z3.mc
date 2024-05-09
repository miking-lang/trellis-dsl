-- Defines a conversion from the set constraint representation used in
-- predecessors.mc to a z3 file, and uses the z3 executable to check whether
-- this is satisfiable.

include "result.mc"
include "sys.mc"

include "repr.mc"

lang TrellisConstraintPrintZ3 = TrellisSetConstraintRepr
  -- Print the declaration and inherent constraints from types for each state
  -- with the given prefix.
  sem z3InherentConstraints : [Int] -> String -> String
  sem z3InherentConstraints stateBounds =
  | prefix ->
    let n = length stateBounds in

    -- Declare the state components as constants in Z3.
    let declConst = lam prefix. lam i.
      let var = concat prefix (int2string i) in
      join ["(declare-const ", var, " Int)"]
    in

    -- Add assertions based on the inherent constraints imposed on each
    -- component of the state based on its type.
    let lowerBoundAssert = lam prefix. lam i.
      let var = concat prefix (int2string i) in
      join ["(assert (>= ", var, " 0))"]
    in
    let upperBoundAssert = lam prefix. lam i.
      let var = concat prefix (int2string i) in
      let ub = int2string (get stateBounds i) in
      join ["(assert (< ", var, " ", ub, "))"]
    in
    let boundAsserts = lam prefix. lam i.
      [lowerBoundAssert prefix i, upperBoundAssert prefix i]
    in
    strJoin "\n"
      (join [create n (declConst prefix), join (create n (boundAsserts prefix))])

  -- Produces a sequence of string representing Z3 expressions corresponding to
  -- the provided predecessor constraints.
  sem z3ComponentConstraints : Map Int (Set PredConstraint) -> String -> [String]
  sem z3ComponentConstraints compConstraints =
  | prefix ->
    let toZ3Constraint = lam idx. lam c.
      let var = concat prefix (int2string idx) in
      map (constraintToZ3Expression var) (setToSeq c)
    in
    join (mapValues (mapMapWithKey toZ3Constraint compConstraints))

  sem constraintToZ3Expression : String -> PredConstraint -> String
  sem constraintToZ3Expression lhs =
  | EqNum (n, _) -> join ["(= ", lhs, " ", int2string n, ")"]
  | NeqNum (n, _) -> join ["(not (= ", lhs, " ", int2string n, "))"]
  | EqYPlusNum (yidx, n, _) ->
    let rhsVar = concat "y" (int2string yidx) in
    join ["(= ", lhs, " (+ ", rhsVar, " ", int2string n, "))"]

  sem z3And : String -> String -> String
  sem z3And l =
  | r -> join ["(and ", l, " ", r, ")"]

  -- Converts the given set constraints in the Trellis model to a
  -- satisfiability problem in Z3. This problem has a solution iff the set
  -- constraint is non-empty.
  sem printZ3NonEmpty : ConstraintRepr -> String
  sem printZ3NonEmpty =
  | {state = state, x = x, y = y} ->
    -- Declare the state component types and introduce their inherent
    -- constraints based on their types.
    let x1 = z3InherentConstraints state "x" in
    let y1 = z3InherentConstraints state "y" in

    -- Convert the explicit constraints imposed on the components of the states
    -- in the provided constraint representation. We assert that the
    -- conjunction of these holds. This is true when there exists at least one
    -- pair of states in the set described by the provided constraints (i.e.,
    -- the formula is satisfiable iff the set is non-empty).
    let x2 = z3ComponentConstraints x "x" in
    let y2 = z3ComponentConstraints y "y" in
    let c = concat x2 y2 in
    let assert =
      if null c then ""
      else join ["(assert ", foldl1 z3And c, ")"]
    in

    -- Build a string from all the above.
    strJoin "\n" [x1, y1, assert, "(check-sat)"]

  -- Converts the given sequence of constraints to a satisfiability problem in
  -- Z3 which has a satisfying solution if there is a to-state not included in
  -- any of the given constraint representations.
  sem printZ3DoesNotCoverAllToStates : [ConstraintRepr] -> String
  sem printZ3DoesNotCoverAllToStates =
  | ([{state = state}] ++ _) & constraintsSeq ->
    -- Add the inherent constraints on the to-state components.
    let inherent= z3InherentConstraints state "y" in

    -- Convert the explicit constraints on the to-state components of each
    -- separate constraint instance to a sequence of Z3 expressions.
    let c = map (lam c. z3ComponentConstraints c.y "y") constraintsSeq in

    -- Assert that none of the provided constraint instances hold (i.e., assert
    -- the negation of their combined Z3 expressions). If Z3 can find a
    -- to-state which is not included in any of the provided constraint
    -- instances, this means they do not cover all to-states.
    let asserts =
      map
        (lam x.
          -- NOTE(larshum, 2024-05-09): If we have no constraints for a
          -- component, we add a false assertion since it implicitly includes
          -- all possible to-states.
          if null x then "(assert false)"
          else join ["(assert (not ", foldl1 z3And x, "))"])
        c
    in

    strJoin "\n" [inherent, strJoin "\n" asserts, "(check-sat)"]
end

lang TrellisConstraintZ3 = TrellisConstraintPrintZ3
  syn Z3Error =
  | UnknownOutput {program : String, stdout : String, stderr : String}
  | NonZeroReturnCode {program : String, stdout : String, stderr : String, code : Int}

  sem printZ3Error : Z3Error -> String
  sem printZ3Error =
  | UnknownOutput t ->
    join [
      "Received unknown output when running z3 on the following program:\n",
      t.program, "\n\nstdout:", t.stdout, "\nstderr:\n", t.stderr ]
  | NonZeroReturnCode t ->
    join [
      "Got return code ", int2string t.code, " from z3 on following program:\n",
      t.program, "\n\nstdout:", t.stdout, "\nstderr:\n", t.stderr ]

  sem eqZ3Error : Z3Error -> Z3Error -> Bool
  sem eqZ3Error l =
  | r ->
    if eqi (constructorTag l) (constructorTag r) then
      eqZ3ErrorH (l, r)
    else false

  sem eqZ3ErrorH : (Z3Error, Z3Error) -> Bool
  sem eqZ3ErrorH =
  | (UnknownOutput l, UnknownOutput r) ->
    if eqString l.program r.program then
      if eqString l.stdout r.stdout then
        eqString l.stderr r.stderr
      else false
    else false
  | (NonZeroReturnCode l, NonZeroReturnCode r) ->
    if eqi l.code r.code then
      if eqString l.program r.program then
        if eqString l.stdout r.stdout then
          eqString l.stderr r.stderr
        else false
      else false
    else false

  sem checkZ3Installed : () -> Bool
  sem checkZ3Installed =
  | _ -> sysCommandExists "z3"

  -- Checks whether the provided constraint representation describing a set of
  -- transitions between pairs of states is empty. We do this by having Z3 find
  -- a satisfying solution to the provided constraints - if there is such a
  -- solution, the set is non-empty.
  sem checkEmpty : ConstraintRepr -> Result () Z3Error Bool
  sem checkEmpty =
  | constraints ->
    let str = printZ3NonEmpty constraints in
    runZ3Program str

  -- Verifies that the given constraints cover all possible values of
  -- to-states.
  sem checkCoversAllToStates : [ConstraintRepr] -> Result () Z3Error Bool
  sem checkCoversAllToStates =
  | constraints ->
    let str = printZ3DoesNotCoverAllToStates constraints in
    runZ3Program str

  sem runZ3Program : String -> Result () Z3Error Bool
  sem runZ3Program =
  | z3Program ->
    let path = sysTempFileMake () in
    writeFile path z3Program;
    let r = sysRunCommand ["z3", path] "" "." in
    deleteFile path;
    if eqi r.returncode 0 then
      switch strTrim r.stdout
      case "sat" then result.ok false
      case "unsat" then result.ok true
      case _ then
        result.err
          (UnknownOutput {program = z3Program, stdout = r.stdout, stderr = r.stderr})
      end
    else
      result.err (NonZeroReturnCode {
        program = z3Program, stdout = r.stdout, stderr = r.stderr,
        code = r.returncode
      })
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
utest checkCoversAllToStates [q3] with result.ok true using eqCheck in
utest checkCoversAllToStates [q4] with result.ok true using eqCheck in
utest checkCoversAllToStates [q3, q4] with result.ok true using eqCheck in
utest checkCoversAllToStates [q5] with result.ok false using eqCheck in
utest checkCoversAllToStates [q4, q5] with result.ok true using eqCheck in
utest checkCoversAllToStates [q6] with result.ok false using eqCheck in
utest checkCoversAllToStates [q5, q6] with result.ok false using eqCheck in
utest checkCoversAllToStates [q5, q6, q8] with result.ok false using eqCheck in

let a = {
  empty with y = mapFromSeq subi [(3, pc [eqn_ 15])]
} in
let b = {
  empty with y = mapFromSeq subi [(3, pc [eqn_ 14])]
} in
let c = {
  empty with y = mapFromSeq subi [(3, pc [neqn_ 14, neqn_ 15])]
} in
utest checkCoversAllToStates [a] with result.ok false using eqCheck in
utest checkCoversAllToStates [b] with result.ok false using eqCheck in
utest checkCoversAllToStates [c] with result.ok false using eqCheck in
utest checkCoversAllToStates [a, b] with result.ok false using eqCheck in
utest checkCoversAllToStates [a, c] with result.ok false using eqCheck in
utest checkCoversAllToStates [b, c] with result.ok false using eqCheck in
utest checkCoversAllToStates [a, b, c] with result.ok true using eqCheck in

let a = {
  empty with y = mapFromSeq subi [(0, pc [eqn_ 0])]
} in
let b = {
  empty with y = mapFromSeq subi [(0, pc [neqn_ 0]), (1, pc [neqn_ 3])]
} in
let c = {
  empty with y = mapFromSeq subi [(0, pc [neqn_ 0]), (1, pc [eqn_ 3])]
} in
utest checkCoversAllToStates [a] with result.ok false using eqCheck in
utest checkCoversAllToStates [b] with result.ok false using eqCheck in
utest checkCoversAllToStates [c] with result.ok false using eqCheck in
utest checkCoversAllToStates [a, b] with result.ok false using eqCheck in
utest checkCoversAllToStates [a, c] with result.ok false using eqCheck in
utest checkCoversAllToStates [b, c] with result.ok false using eqCheck in
utest checkCoversAllToStates [a, b, c] with result.ok true using eqCheck in

()
