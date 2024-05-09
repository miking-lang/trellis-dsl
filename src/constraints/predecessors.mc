-- Given that all condition expressions used in set constraints are of a simple
-- format, we generate code to compute the predecessors at runtime instead of
-- using a lookup table of predecessors computed ahead of time. This leads to
-- better performance for larger models.

include "../model/ast.mc"
include "../model/encode.mc"
include "compile.mc"
include "propagate.mc"
include "repr.mc"
include "z3.mc"

lang TrellisConstraintZ3Analysis =
  TrellisConstraintZ3 + TrellisModelCompileSetConstraintError

  syn ConstraintError =
  | IntersectingSetConstraints [Info]
  | EmptySetConstraint Info
  | Z3FailError String

  sem printConstraintErrorMessage warning =
  | IntersectingSetConstraints i ->
    printSection warning i "Set constraints are not disjoint"
  | EmptySetConstraint i ->
    printSection true [i] "Set constraint describes an empty set"
  | Z3FailError s -> s

  sem eqConstraintErrorH =
  | (IntersectingSetConstraints li, IntersectingSetConstraints ri) ->
    eqSeq (lam l. lam r. eqi (infoCmp l r) 0) li ri
  | (EmptySetConstraint li, EmptySetConstraint ri) -> eqi (infoCmp li ri) 0
  | (Z3FailError ls, Z3FailError rs) -> eqString ls rs

  sem z3Error : [Z3Error] -> ConstraintError
  sem z3Error =
  | errs -> Z3FailError (strJoin "\n" (map printZ3Error errs))

  -- Verifies that each set constraint described by a corresponding constraint
  -- representation is non-empty. If it is not, we produce a warning.
  sem verifyNonEmptySetConstraints : [ConstraintRepr] -> ConstraintResult [ConstraintRepr]
  sem verifyNonEmptySetConstraints =
  | setConstraints ->
    let checkNonempty = lam acc. lam i. lam c.
      switch result.consume (checkEmpty c)
      case (_, Right true) then
        result.withAnnotations (result.warn (EmptySetConstraint c.info)) acc
      case (_, Right false) then
        acc
      case (_, Left errs) then
        result.withAnnotations (result.err (z3Error errs)) acc
      end
    in
    if checkZ3Installed () then
      foldli checkNonempty (result.ok setConstraints) setConstraints
    else result.err (Z3FailError "Could not find command 'z3'")

  -- Verifies that all pairs of set constraints are disjoint from each other.
  -- This is a prerequisite for the CUDA code generation.
  sem verifyDisjointSetConstraints : [ConstraintRepr]
                                  -> ConstraintResult [ConstraintRepr]
  sem verifyDisjointSetConstraints =
  | constraints ->
    let checkDisjoint = lam acc. lam lhs. lam rhs.
      switch result.consume (disjointConstraints lhs rhs)
      case (_, Right true) then acc
      case (_, Right false) then
        let infos = [lhs.info, rhs.info] in
        result.withAnnotations (result.err (IntersectingSetConstraints infos)) acc
      case (_, Left errs) then
        result.withAnnotations (result.err (z3Error errs)) acc
      end
    in
    if checkZ3Installed () then
      foldli
        (lam acc. lam idx. lam c1.
          let rhs = subsequence constraints (addi idx 1) (length constraints) in
          foldl
            (lam acc. lam c2. checkDisjoint acc c1 c2)
            acc rhs)
        (result.ok constraints) constraints
    else result.err (Z3FailError "Could not find command 'z3'")

  -- Determines whether two given environments containing constraints are
  -- disjoint, i.e., if they describe set constraints with no transitions in
  -- common. We do this by taking the union of the constraints on their
  -- from-states and to-states, looking for a contradiction. They are not
  -- disjoint if we can find a valid choice of each component, satisfying the
  -- united constraints.
  sem disjointConstraints : ConstraintRepr -> ConstraintRepr -> Result () Z3Error Bool
  sem disjointConstraints lhs =
  | rhs ->
    let union = {
      state = lhs.state,
      x = mapUnionWith setUnion lhs.x rhs.x,
      y = mapUnionWith setUnion lhs.y rhs.y,
      info = mergeInfo lhs.info rhs.info
    } in
    checkEmpty union

  -- As above, but considers only the constraints imposed on the to-states,
  -- meaning we treat the from-state as if it had no constraints.
  sem disjointToStateConstraints : ConstraintRepr -> ConstraintRepr -> Result () Z3Error Bool
  sem disjointToStateConstraints lhs =
  | rhs ->
    let c = {
      state = lhs.state,
      x = mapEmpty subi,
      y = mapUnionWith setUnion lhs.y rhs.y,
      info = mergeInfo lhs.info rhs.info
    } in
    checkEmpty c
end

lang TrellisModelPredecessorAnalysis =
  TrellisConstraintPropagation + TrellisConstraintZ3Analysis +
  TrellisModelAst + TrellisTypeCardinality

  sem performPredecessorAnalysis : TrellisOptions -> TModel -> Option [ConstraintRepr]
  sem performPredecessorAnalysis options =
  | model ->
    performPredecessorAnalysisH options model.stateType model.transition

  sem performPredecessorAnalysisH : TrellisOptions -> TType -> TransitionProbDef
                                 -> Option [ConstraintRepr]
  sem performPredecessorAnalysisH options stateType =
  | {cases = cases, info = info} ->
    let res = result.mapM (lam c. setConstraintToRepr stateType c.cond) cases in
    let res = result.map (map propagateConstraints) res in
    let res = result.bind res verifyNonEmptySetConstraints in
    let res = result.bind res verifyDisjointSetConstraints in
    switch result.consume res
    case (warnings, Right reprs) then
      printAnalysisWarningMessages warnings;
      Some reprs
    case (warnings, Left errors) then
      printAnalysisWarningMessages warnings;
      if options.errorPredecessorAnalysis then
        printAnalysisErrorMessage false errors;
        exit 1
      else if options.warnPredecessorAnalysis then
        printAnalysisErrorMessage true errors;
        None ()
      else
        None ()
    end

  sem printAnalysisWarningMessages : [ConstraintError] -> ()
  sem printAnalysisWarningMessages =
  | warnings ->
    if null warnings then () else
    let strs = strJoin "\n" (map (printConstraintErrorMessage true) warnings) in
    printLn strs

  sem printAnalysisErrorMessage : Bool -> [ConstraintError] -> ()
  sem printAnalysisErrorMessage warning =
  | errors ->
    let errStrs = strJoin "\n" (map (printConstraintErrorMessage warning) errors) in
    let fallbackStr =
      if warning then "\nFalling back to pre-computing predecessors"
      else ""
    in
    let msg = join [
      "Predecessor analysis failed\n",
      errStrs,
      fallbackStr,
      "\n"
    ] in
    if warning then print msg
    else printError "\n"
end

lang TestLang = TrellisConstraintZ3Analysis + ConstraintTestLang end

mexpr

use TestLang in

let eqUnwrappedLhs = lam eqf. lam l. lam r.
  match result.consume l with (_, Right v) then
    eqf v r
  else false
in
let isError = lam l. lam.
  optionIsNone (result.toOption l)
in

let int_ = lam n. TInt {bounds = Some (0, n), info = NoInfo ()} in
let stateType = TTuple {tys = [int_ 2, int_ 6], info = NoInfo ()} in
let pc = setOfSeq cmpPredConstraint in
let c1 = defaultConstraintRepr (NoInfo ()) stateType in
let c2 = {
  c1 with x = mapFromSeq subi [(0, pc [EqNum (0, NoInfo ()), NeqNum (0, NoInfo ())])]
} in
let c3 = {
  c1 with x = mapFromSeq subi [(0, pc [EqNum (0, NoInfo ())])]
} in
utest verifyNonEmptySetConstraints [c1, c2, c3]
with ([EmptySetConstraint (NoInfo ())], [c1, c2, c3])
using lam l. lam r.
  match result.consume l with (warns, Right v) then
    if eqSeq eqConstraintError warns r.0 then eqSeq eqConstraints v r.1
    else false
  else false
in

utest verifyDisjointSetConstraints [c1, c2, c3] with () using isError in

()
