-- Given that all condition expressions used in set constraints are of a simple
-- format, we generate code to compute the predecessors at runtime instead of
-- using a lookup table of predecessors computed ahead of time. This leads to
-- better performance for larger models.

include "../model/ast.mc"
include "../model/encode.mc"
include "compile.mc"
include "repr.mc"
include "simplify.mc"
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
  | (Z3FailError ls, Z3FailError rs) -> eqString ls rs

  sem z3Error : [Z3Error] -> ConstraintError
  sem z3Error =
  | errs -> Z3FailError (strJoin "\n" (map printZ3Error errs))

  -- Verifies that each set constraint described by a corresponding constraint
  -- representation is non-empty. If it is not, we produce a warning.
  sem verifyNonempty : [ConstraintRepr] -> ConstraintResult [ConstraintRepr]
  sem verifyNonempty =
  | setConstraints ->
    let checkNonempty = lam acc. lam c.
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
      foldl checkNonempty (result.ok setConstraints) setConstraints
    else result.err (Z3FailError "Could not find command 'z3'")

  -- Verifies that all pairs of set constraints are disjoint from each other.
  -- This is a prerequisite for the CUDA code generation.
  sem verifyDisjointSetConstraints : [ConstraintRepr] -> ConstraintResult [ConstraintRepr]
  sem verifyDisjointSetConstraints =
  | setConstraints ->
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
          let rhs = subsequence setConstraints (addi idx 1) (length setConstraints) in
          foldl
            (lam acc. lam c2. checkDisjoint acc c1 c2)
            acc rhs)
        (result.ok setConstraints) setConstraints
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
  TrellisConstraintSimplification + TrellisConstraintZ3Analysis +
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
    let res = result.bind res verifyNonempty in
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
