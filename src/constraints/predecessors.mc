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

  -- As above, but considers only the constraints imposed on the to-states,
  -- meaning we treat the from-state as if it had no constraints.
  sem disjointTargetStateConstraints : ConstraintRepr -> ConstraintRepr -> Result () Z3Error Bool
  sem disjointTargetStateConstraints lhs =
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
    else printError msg
end
