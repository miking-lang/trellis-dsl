-- Defines a conversion from the set constraint representation used in
-- predecessors.mc to a z3 file, and uses the z3 executable to check whether
-- this is satisfiable.

include "result.mc"
include "sys.mc"

include "repr.mc"

lang TrellisConstraintPrintZ3 = TrellisSetConstraintRepr

  -- Converts the environment representing a set constraint in the Trellis
  -- model to a satisfiability problem expressed in Z3. This problem has a
  -- solution when the set constraint is non-empty.
  sem printZ3Satisfiability : ConstraintRepr -> String
  sem printZ3Satisfiability =
  | {state = state, x = x, y = y} ->
    let n = length state in

    -- Declarations of the state components.
    let declConst = lam prefix. lam i.
      let var = concat prefix (int2string i) in
      join ["(declare-const ", var, " Int)"]
    in
    let xdecls = create n (declConst "x") in
    let ydecls = create n (declConst "y") in

    -- Assertions based on the inherent constraints imposed on each component
    -- based on its type.
    let lowerBoundAssert = lam prefix. lam i.
      let var = concat prefix (int2string i) in
      join ["(assert (>= ", var, " 0))"]
    in
    let upperBoundAssert = lam prefix. lam i.
      let var = concat prefix (int2string i) in
      let ub = int2string (get state i) in
      join ["(assert (< ", var, " ", ub, "))"]
    in
    let boundAsserts = lam prefix. lam i.
      [lowerBoundAssert prefix i, upperBoundAssert prefix i]
    in
    let xbounds = join (create n (boundAsserts "x")) in
    let ybounds = join (create n (boundAsserts "y")) in

    -- Additional assertions based on the constraints defined on the from-state
    -- (x) and the to-state (y).
    let addConstraintAssert = lam prefix. lam acc. lam idx. lam c.
      let var = concat prefix (int2string idx) in
      concat acc (map (constraintToAssert var) (setToSeq c))
    in
    let xconstraints = mapFoldWithKey (addConstraintAssert "x") [] x in
    let yconstraints = mapFoldWithKey (addConstraintAssert "y") [] y in

    -- Specify that we want to check for satisfiability.
    let checkSat = "(check-sat)" in

    -- Build a string from all the above.
    strJoin "\n" (join [xdecls, ydecls, xbounds, ybounds, xconstraints, yconstraints, [checkSat]])

  sem constraintToAssert : String -> PredConstraint -> String
  sem constraintToAssert lhs =
  | EqNum (n, _) -> join ["(assert (= ", lhs, " ", int2string n, "))"]
  | NeqNum (n, _) -> join ["(assert (not (= ", lhs, " ", int2string n, ")))"]
  | EqYPlusNum (yidx, n, _) ->
    let rhsVar = concat "y" (int2string yidx) in
    join ["(assert (= ", lhs, " (+ ", rhsVar, " ", int2string n, ")))"]
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

  -- Checks whether the given environment of constraints describes the empty
  -- set. We use this to check whether sets of constraints are disjoint (via
  -- intersection).
  sem checkEmpty : ConstraintRepr -> Result () Z3Error Bool
  sem checkEmpty =
  | constraints ->
    let str = printZ3Satisfiability constraints in
    let path = sysTempFileMake () in
    writeFile path str;
    let r = sysRunCommand ["z3", path] "" "." in
    deleteFile path;
    if eqi r.returncode 0 then
      switch strTrim r.stdout
      case "sat" then result.ok false
      case "unsat" then result.ok true
      case _ then
        result.err (UnknownOutput {program = str, stdout = r.stdout, stderr = r.stderr})
      end
    else
      result.err (NonZeroReturnCode {
        program = str, stdout = r.stdout, stderr = r.stderr,
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

let pc = setOfSeq cmpPredConstraint in
let empty = {
  state = [4, 4, 4, 16],
  x = mapEmpty subi, y = mapEmpty subi, info = NoInfo ()
} in

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

let y = mapFromSeq subi [
  (3, pc [neqn_ 15, neqn_ 14])
] in
let rhs2 = {
  empty with x = x, y = y
} in

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

()
