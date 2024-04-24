-- Given that all condition expressions used in set constraints are of a simple
-- format, we generate code to compute the predecessors at runtime instead of
-- using a lookup table of predecessors computed ahead of time. This leads to
-- better performance for larger models.

include "../model/ast.mc"
include "../model/encode.mc"
include "repr.mc"
include "simplify.mc"
include "z3.mc"

lang TrellisConstraintDisjoint =
  TrellisConstraintZ3 + TrellisModelCompileSetConstraintError

  syn ConstraintError =
  | IntersectingSetConstraints Info
  | Z3Error String

  sem constraintErrorInfo =
  | IntersectingSetConstraints i -> i
  | Z3Error _ -> NoInfo ()

  sem printConstraintError =
  | IntersectingSetConstraints i ->
    infoErrorString i "Set constraints are not disjoint"
  | Z3Error s -> s

  sem ensureDisjointSetConstraints : [ConstraintRepr]
                                  -> Result () ConstraintError [ConstraintRepr]
  sem ensureDisjointSetConstraints =
  | setConstraints ->
    let checkDisjoint = lam acc. lam lhs. lam rhs.
      switch result.consume (disjointConstraints lhs rhs)
      case (_, Right true) then acc
      case (_, Right false) then
        let info = mergeInfo lhs.info rhs.info in
        result.withAnnotations (result.err (IntersectingSetConstraints info)) acc
      case (_, Left z3errs) then
        let err = Z3Error (strJoin "\n" (map printZ3Error z3errs)) in
        result.withAnnotations (result.err err) acc
      end
    in
    foldli
      (lam acc. lam idx. lam c1.
        let rhs = subsequence setConstraints (addi idx 1) (length setConstraints) in
        foldl
          (lam acc. lam c2. checkDisjoint acc c1 c2)
          acc rhs)
      (result.ok setConstraints) setConstraints

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
  TrellisConstraintSimplification + TrellisConstraintDisjoint +
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
    let res = result.bind res ensureDisjointSetConstraints in
    switch result.consume res
    case (_, Right reprs) then Some reprs
    case (_, Left errors) then
      if options.errorPredecessorAnalysis then
        printAnalysisErrorMessage true errors;
        exit 1
      else if options.warnPredecessorAnalysis then
        printAnalysisErrorMessage false errors;
        None ()
      else
        None ()
    end

  sem printAnalysisErrorMessage : Bool -> [ConstraintError] -> ()
  sem printAnalysisErrorMessage terminating =
  | errors ->
    let errStrs = strJoin "\n" (map printConstraintError errors) in
    let fallbackStr =
      if terminating then ""
      else "\nFalling back to pre-computing predecessors"
    in
    let msg = join [
      "Predecessor analysis failed due to the following errors:\n",
      errStrs,
      fallbackStr
    ] in
    printLn msg
end
