-- Given that all condition expressions used in set constraints are of a simple
-- format, we generate code to compute the predecessors at runtime instead of
-- using a lookup table of predecessors computed ahead of time. This leads to
-- better performance for larger models.

include "ast.mc"
include "pprint.mc"

lang TrellisModelPredecessorAnalysis = TrellisModelAst + TrellisModelPrettyPrint
  syn PredId =
  | EqNum Int
  | NeqNum Int
  | EqYPlusNum (Int, Int)
  | X Int
  | Y Int

  sem cmpPredId : PredId -> PredId -> Int
  sem cmpPredId l =
  | r ->
    let lt = constructorTag l in
    let rt = constructorTag r in
    if eqi lt rt then cmpPredIdH (l, r)
    else subi lt rt

  sem cmpPredIdH : (PredId, PredId) -> Int
  sem cmpPredIdH =
  | (EqNum l, EqNum r) -> subi l r
  | (NeqNum l, NeqNum r) -> subi l r
  | (EqYPlusNum l, EqYPlusNum r) ->
    let c = subi l.0 r.0 in
    if eqi c 0 then subi l.1 r.1 else c
  | (X l, X r) -> subi l r
  | (Y l, Y r) -> subi l r

  type AnalysisEnv = Map PredId [PredId]

  sem performAnalysis : TModel -> ()
  sem performAnalysis =
  | model ->
    performAnalysisH model.stateType model.transition

  sem performAnalysisH : TType -> TransitionProbDef -> ()
  sem performAnalysisH stateType =
  | {x = x, y = y, cases = cases, info = info} ->
    iter
      (lam c.
        let env = performCaseAnalysis (mapEmpty cmpPredId) c.cond in
        dprintLn (mapBindings env))
      cases;
    ()

  sem performCaseAnalysis : AnalysisEnv -> TSet -> AnalysisEnv
  sem performCaseAnalysis env =
  | SAll _ -> error "Set containing all transitions not supported yet"
  | SValueBuilder _ -> error "Set containing fixed values not supported yet"
  | STransitionBuilder {x = x, y = y, conds = conds} ->
    foldl (performConditionAnalysis x y) env conds

  sem performConditionAnalysis : Name -> Name -> AnalysisEnv -> TExpr -> AnalysisEnv
  sem performConditionAnalysis x y env =
  | EBinOp {
      op = op & (OEq _ | ONeq _),
      lhs = ESlice {target = EVar {id = id}, lo = lo, hi = hi, info = info},
      rhs = EInt {i = i}
    }
  | EBinOp {
      op = op & (OEq _ | ONeq _),
      lhs = EInt {i = i},
      rhs = ESlice {target = EVar {id = id}, lo = lo, hi = hi, info = info}
    } ->
    if eqi lo hi then
      let idx =
        if nameEq id x then X lo
        else if nameEq id y then Y lo
        else errorSingle [info] "Name refers to neither from-state nor to-state"
      in
      let value =
        match op with OEq _ then EqNum i
        else match op with ONeq _ then NeqNum i
        else never
      in
      mapInsertWith concat idx [value] env
    else error "Analysis only works on single components, not slices"
  | EBinOp {
      op = OEq (),
      lhs = ESlice {target = EVar {id = id1}, lo = lo1, hi = hi1},
      rhs = ESlice {target = EVar {id = id2}, lo = lo2, hi = hi2}
    } ->
    if and (eqi lo1 hi1) (eqi lo2 hi2) then
      match
        if and (nameEq id1 x) (nameEq id2 y) then Some (lo1, lo2)
        else if and (nameEq id2 x) (nameEq id1 y) then Some (lo2, lo1)
        else None ()
      with Some (xidx, yidx) then
        mapInsertWith concat (X xidx) [Y yidx] env
      else env
    else error "Analysis only works on single components, not slices"
  | EBinOp {
      op = OEq (),
      lhs = ESlice {target = EVar {id = id1}, lo = lo1, hi = hi1, ty = ty},
      rhs = EBinOp {
        op = OAdd (),
        lhs = ESlice {target = EVar {id = id2}, lo = lo2, hi = hi2},
        rhs = EInt {i = n}}
    } ->
    if and (eqi lo1 hi1) (eqi lo2 hi2) then
      match
        if and (nameEq id1 x) (nameEq id2 y) then Some (lo1, lo2, n)
        else if and (nameEq id2 x) (nameEq id1 y) then Some (lo2, lo1, negi n)
        else None ()
      with Some (xidx, yidx, n) then
        match ty with TInt {bounds = Some (lo, hi)} then
          let env = mapInsertWith concat (X xidx) [EqYPlusNum (yidx, n)] env in
          let ub = subi hi n in
          if gti n 0 then
            foldl
              (lam env. lam i. mapInsertWith concat (Y yidx) [NeqNum i] env)
              env
              (create (subi hi ub) (lam i. subi hi i))
          else env
        else error "Invalid type of target"
      else error "Failed to apply analysis"
    else error "Analysis only works on single components, not slices"
  | _ -> env
end
