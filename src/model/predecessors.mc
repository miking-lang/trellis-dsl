-- Given that all condition expressions used in set constraints are of a simple
-- format, we generate code to compute the predecessors at runtime instead of
-- using a lookup table of predecessors computed ahead of time. This leads to
-- better performance for larger models.

include "ast.mc"
include "encode.mc"
include "eq.mc"
include "pprint.mc"

lang TrellisModelPredecessorBase
  syn PredConstraint =
  | EqNum Int
  | NeqNum Int
  | EqYPlusNum (Int, Int)

  sem printPredConstraint : PredConstraint -> String
  sem printPredConstraint =
  | EqNum n -> concat " == " (int2string n)
  | NeqNum n -> concat " != " (int2string n)
  | EqYPlusNum (idx, n) ->
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
  | (EqNum ln, EqNum rn) -> subi ln rn
  | (NeqNum ln, NeqNum rn) -> subi ln rn
  | (EqYPlusNum (ly, ln), EqYPlusNum (ry, rn)) ->
    let c = subi ly ry in
    if eqi c 0 then subi ln rn else c

  sem singletonConstraint : PredConstraint -> Set PredConstraint
  sem singletonConstraint =
  | c -> setOfSeq cmpPredConstraint [c]

  type AnalysisEnv = {
    state : [Int],
    x : Map Int (Set PredConstraint),
    y : Map Int (Set PredConstraint)
  }

  sem printAnalysisEnv : AnalysisEnv -> String
  sem printAnalysisEnv =
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

lang TrellisModelPredecessorConstraintSimplification =
  TrellisModelPredecessorBase

  sem simplifyConstraints : AnalysisEnv -> Option AnalysisEnv
  sem simplifyConstraints =
  | env ->
    match simplifyFromStateConstraints env with Some env then
      simplifyToStateConstraints env
    else None ()

  sem simplifyFromStateConstraints : AnalysisEnv -> Option AnalysisEnv
  sem simplifyFromStateConstraints =
  | env ->
    let simplifyConstraints = lam env. lam idx. lam c.
      -- 1. Propagate literal constraints on the from-state to the
      --    constraints on to-state, and propagate the to-state constraints
      --    pairwise to each other as well as individually.
      match propagateFromStateConstraints env c with Some env then
        -- 2. Validate the literal equality constraints. The result depends on
        --    how many equality constraints we have:
        --    - If we have zero, the equal literal is -1, and all constraints
        --      are returned.
        --    - If we have one, this literal value is returned along with the
        --      remaining constraints.
        --    - If we have more than one, we have a contradiction.
        match validateLiteralEqualityConstraints env idx c with Some (eqn, rest) then
          if eqi eqn -1 then
            -- 3. If we have no literal equality constraints, and we have at
            --    least one constraint related to the to-state, we remove all
            --    constraints but one of the to-state relations. Otherwise, we
            --    keep the inequality constraints (only).
            let c =
              match pickFirstToStateConstraint rest with Some c then
                singletonConstraint c
              else keepInequalityConstraints rest
            in
            Some {env with x = mapInsert idx c env.x}
          else
            -- 4. If we have a literal equality constraint, we eliminate all
            --    inequality constraints (while ensuring we have no
            --    contradiction). The result is that we only have one literal
            --    equality constraint.
            match eliminateInequalityConstraints eqn rest with Some c then
              let v = singletonConstraint (EqNum eqn) in
              Some {env with x = mapInsert idx v env.x}
            else None ()
        else None ()
      else None ()
    in
    mapFoldlOption simplifyConstraints env env.x

  sem propagateFromStateConstraints : AnalysisEnv -> Set PredConstraint
                                   -> Option AnalysisEnv
  sem propagateFromStateConstraints env =
  | constraints ->
    let isLiteralConstraint = lam c.
      match c with EqNum _ | NeqNum _ then true
      else false
    in
    let propagateLiteralConstraints = lam litConstraints. lam env. lam c.
      match c with EqYPlusNum (yidx, n) then
        optionFoldlM (propagateLiteralConstraint yidx n) env litConstraints
      else error (concat "Unexpected non-literal constraint: " (printPredConstraint c))
    in
    match partition isLiteralConstraint (setToSeq constraints)
    with (literalConstraints, toStateConstraints) in

    -- 1. Propagate every literal constraint to each of the to-state components
    -- referred to in the to-state constraints.
    match optionFoldlM (propagateLiteralConstraints literalConstraints) env toStateConstraints
    with Some env then
      -- 2. Propagate constraints on the to-state for each pair of constraints
      -- on the from-state expressed in terms of the to-state.
      match propagatePairwiseToConstraints env toStateConstraints with Some env then
        -- 3. Propagate constraints directly from each to-state, based on the
        -- fact that they are only valid when the corresponding x-value is
        -- within its bounds.
        Some (foldl propagateBoundConstraint env toStateConstraints)
      else None ()
    else None ()

  sem propagateLiteralConstraint : Int -> Int -> AnalysisEnv
                                -> PredConstraint -> Option AnalysisEnv
  sem propagateLiteralConstraint yidx yn env =
  | EqNum n ->
    let ymaxval = get env.state yidx in
    let np = subi n yn in
    -- NOTE(larshum, 2024-04-23): A literal equality constraint must be within
    -- the valid range of the type.
    if and (geqi np 0) (lti np ymaxval) then
      let yconstraint = singletonConstraint (EqNum np) in
      Some {env with y = mapInsertWith setUnion yidx yconstraint env.y}
    else None ()
  | NeqNum n ->
    let np = subi n yn in
    let yconstraint = singletonConstraint (NeqNum np) in
    Some {env with y = mapInsertWith setUnion yidx yconstraint env.y}

  sem propagatePairwiseToConstraints : AnalysisEnv -> [PredConstraint]
                                    -> Option AnalysisEnv
  sem propagatePairwiseToConstraints env =
  | toConstraints ->
    let propagateConstraints = lam env. lam idxc.
      match idxc with (index, c) in
      -- NOTE(larshum, 2024-04-23): In the below line, we pick all constraints
      -- beyond the current one in the sequence. This is to go through all
      -- pairs of constraints.
      let rhs = subsequence toConstraints (addi index 1) (length toConstraints) in
      optionFoldlM (lam env. lam c2. propagateConstraint env (c, c2)) env rhs
    in
    let indexedConstraints = mapi (lam idx. lam x. (idx, x)) toConstraints in
    optionFoldlM propagateConstraints env indexedConstraints

  sem propagateConstraint : AnalysisEnv -> (PredConstraint, PredConstraint)
                         -> Option AnalysisEnv
  sem propagateConstraint env =
  | (EqYPlusNum (lidx, ln), EqYPlusNum (ridx, rn)) ->
    let n = subi rn ln in
    match
      if lti n 0 then (negi n, lidx, ridx)
      else (n, ridx, lidx)
    with (n, srcIdx, dstIdx) in
    let ymax = get env.state srcIdx in
    if and (geqi n 0) (lti n ymax) then
      let c = singletonConstraint (EqYPlusNum (srcIdx, n)) in
      Some {env with y = mapInsertWith setUnion dstIdx c env.y}
    else None ()
  | (l, r) ->
    error (join [
      "Unexpected constraints: ", printPredConstraint l, " and ",
      printPredConstraint r
    ])

  sem propagateBoundConstraint : AnalysisEnv -> PredConstraint -> AnalysisEnv
  sem propagateBoundConstraint env =
  | EqYPlusNum (yidx, n) ->
    let maxv = get env.state yidx in
    let invalidValues =
      if lti n 0 then create n (lam i. i)
      else create n (lam i. subi (subi maxv i) 1)
    in
    let c = setOfSeq cmpPredConstraint (map (lam n. NeqNum n) invalidValues) in
    {env with y = mapInsertWith setUnion yidx c env.y}
  | c ->
    error (concat "Unexpected constraint on to-state: " (printPredConstraint c))

  sem validateLiteralEqualityConstraints : AnalysisEnv -> Int -> Set PredConstraint
                                        -> Option (Int, Set PredConstraint)
  sem validateLiteralEqualityConstraints env idx =
  | constraints ->
    let eqLit = lam c.
      match c with EqNum n then Some n else None ()
    in
    let eqc = mapOption eqLit (setToSeq constraints) in
    -- NOTE(larshum, 2024-04-23): If we have more than one literal equality
    -- constraint, this is a contradiction. We also have a contradiction if the
    -- literal value is outside of its valid range.
    match eqc with [] then Some (-1, constraints)
    else match eqc with [n] then
      let maxval = get env.state idx in
      if and (geqi n 0) (lti n maxval) then
        Some (n, setRemove (EqNum n) constraints)
      else None ()
    else None ()

  sem eliminateInequalityConstraints : Int -> Set PredConstraint -> Option (Set PredConstraint)
  sem eliminateInequalityConstraints eqn =
  | constraints ->
    let neqLitConstraint = lam c.
      match c with NeqNum _ then true else false
    in
    let compareInequality = lam c.
      match c with NeqNum n then neqi n eqn
      else error (concat "Invalid inequality constraint: " (printPredConstraint c))
    in
    match partition neqLitConstraint (setToSeq constraints)
    with (neqc, rest) in
    -- NOTE(larshum, 2024-04-23): If all inequality constraints are on distinct
    -- literals from the equality constraint, we can remove them. Otherwise, we
    -- have an equality and inequality constraint on the same value, which is
    -- invalid.
    if forAll compareInequality neqc then
      Some (setOfSeq cmpPredConstraint rest)
    else None ()

  sem pickFirstToStateConstraint : Set PredConstraint -> Option PredConstraint
  sem pickFirstToStateConstraint =
  | constraints ->
    let someIfToStateConstraint = lam c.
      match c with EqYPlusNum _ then Some c else None ()
    in
    let toStateConstraints = mapOption someIfToStateConstraint (setToSeq constraints) in
    if null toStateConstraints then None ()
    else Some (head toStateConstraints)

  sem keepInequalityConstraints : Set PredConstraint -> Set PredConstraint
  sem keepInequalityConstraints =
  | constraints ->
    let isInequalityConstraint = lam c.
      match c with NeqNum _ then true else false
    in
    mapFilterWithKey (lam c. lam. isInequalityConstraint c) constraints

  sem removeContradictoryInequalityConstraints : Int -> Set PredConstraint
                                              -> Set PredConstraint
  sem removeContradictoryInequalityConstraints maxv =
  | constraints ->
    let isContradictoryInequality = lam c.
      match c with NeqNum n then or (lti n 0) (geqi n maxv) else false
    in
    mapFilterWithKey (lam c. lam. not (isContradictoryInequality c)) constraints

  sem simplifyToStateConstraints : AnalysisEnv -> Option AnalysisEnv
  sem simplifyToStateConstraints =
  | env ->
    let simplifyConstraints = lam env. lam idx. lam c.
      -- 1. Remove inequallity constraints that are contradictory due to being
      --    negative or beyond the range of the type.
      let maxv = get env.state idx in
      let c = removeContradictoryInequalityConstraints maxv c in

      -- 2. Validate the literal equality constraints (as for the from-state).
      match validateLiteralEqualityConstraints env idx c with Some (eqn, rest) then
        if eqi eqn -1 then
          Some {env with y = mapInsert idx rest env.y}
        else
          -- 3. If we have a literal equality constraint, we remove all
          --    inequality constraints and ensure these do not contradict the
          --    equality constraint.
          match eliminateInequalityConstraints eqn rest with Some c then
            let v = setInsert (EqNum eqn) c in
            Some {env with y = mapInsert idx v env.y}
          else None ()
      else None ()
    in
    mapFoldlOption simplifyConstraints env env.y
end

lang TrellisModelPredecessorAnalysis =
  TrellisModelPredecessorBase + TrellisModelPredecessorConstraintSimplification +
  TrellisModelAst + TrellisTypeCardinality

  sem performAnalysis : TModel -> ()
  sem performAnalysis =
  | model ->
    performAnalysisH model.stateType model.transition

  sem performAnalysisH : TType -> TransitionProbDef -> ()
  sem performAnalysisH stateType =
  | {x = x, y = y, cases = cases, info = info} ->
    -- NOTE(larshum, 2024-04-23): We assume all components of the state type
    -- have been transformed to be values in the range [0, n), where 'n' is the
    -- upper bound. We represent the state by these upper bounds, computed as
    -- the cardinality of the type of the component.
    let state =
      match stateType with TTuple {tys = tys} then map cardinalityType tys
      else [cardinalityType stateType]
    in
    let emptyEnv = {state = state, x = mapEmpty subi, y = mapEmpty subi} in
    -- TODO: complete the implementation by reaching some kind of
    -- conclusions...
    iter
      (lam c.
        let env = performCaseAnalysis emptyEnv c.cond in
        printLn (printAnalysisEnv env))
      cases;
    ()

  sem performCaseAnalysis : AnalysisEnv -> TSet -> AnalysisEnv
  sem performCaseAnalysis env =
  | SAll _ -> error "Set containing all transitions not supported yet"
  | SValueBuilder _ -> error "Set containing fixed values not supported yet"
  | STransitionBuilder {x = x, y = y, conds = conds} ->
    let env = foldl (performConditionAnalysis x y) env conds in
    match simplifyConstraints env with Some env then env
    else error "Found inconsistency when simplifying constraints"

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
      let idx = lo in
      let value =
        match op with OEq _ then EqNum i
        else match op with ONeq _ then NeqNum i
        else never
      in
      let v = setOfSeq cmpPredConstraint [value] in
      if nameEq id x then
        {env with x = mapInsertWith setUnion idx v env.x}
      else if nameEq id y then
        {env with y = mapInsertWith setUnion idx v env.y}
      else errorSingle [info] "Name refers to neither from-state nor to-state"
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
        let v = setOfSeq cmpPredConstraint [EqYPlusNum (yidx, 0)] in
        {env with x = mapInsertWith concat xidx v env.x}
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
          let c = singletonConstraint (EqYPlusNum (yidx, n)) in
          {env with x = mapInsertWith setUnion xidx c env.x}
        else error "Invalid type of target"
      else error "Failed to apply analysis"
    else error "Analysis only works on single components, not slices"
  | _ -> env
end

lang TestLang =
  TrellisModelPredecessorAnalysis + TrellisModelEq + TrellisModelPrettyPrint
end


mexpr

use TestLang in

let eqConstraints = mapEq setEq in
let ppConstraints = lam l. lam r.
  let pp = printAnalysisEnv in
  utestDefaultToString pp pp l r
in
let eqc = lam l. lam r.
  switch (l, r)
  case (Some lhs, Some rhs) then
    if eqConstraints lhs.x rhs.x then
      eqConstraints lhs.y rhs.y
    else false
  case (None _, None _) then true
  case _ then false
  end
in
let ppc = lam l. lam r.
  let pp = lam o.
    match o with Some c then join ["Some (", printAnalysisEnv c, ")"]
    else "None"
  in
  utestDefaultToString pp pp l r
in
let pc = setOfSeq cmpPredConstraint in

let empty = {
  state = [4, 4, 4, 16],
  x = mapEmpty subi,
  y = mapEmpty subi
} in
utest simplifyConstraints empty with Some empty using eqc else ppc in

let valid = {
  empty with x = mapFromSeq subi [(0, pc [EqNum 1])]
} in
utest simplifyConstraints valid with Some valid using eqc else ppc in

let inconsistent = {
  empty with x = mapFromSeq subi [(0, pc [EqNum 1, EqNum 2])]
} in
utest simplifyConstraints inconsistent with None () using eqc else ppc in

let xconstr = {
  empty with x = mapFromSeq subi [(0, pc [EqNum 1, NeqNum 2])]
} in
utest simplifyConstraints xconstr with Some valid using eqc else ppc in

let manyneqelim = {
  empty with x = mapFromSeq subi [(3, pc [EqNum 1, NeqNum 5, NeqNum 7, NeqNum 4, NeqNum 9])]
} in
let expected = {
  empty with x = mapFromSeq subi [(3, pc [EqNum 1])]
} in
utest simplifyConstraints manyneqelim with Some expected using eqc else ppc in

let yconstr = {
  empty with x = mapFromSeq subi [(0, pc [EqNum 1, EqYPlusNum (2, 0)])]
} in
let expected = {
  empty with x = mapFromSeq subi [(0, pc [EqNum 1])],
             y = mapFromSeq subi [(2, pc [EqNum 1])]
} in
utest simplifyConstraints yconstr with Some expected using eqc else ppc in

let yconstr2 = {
  empty with x = mapFromSeq subi [(0, pc [EqNum 1, EqYPlusNum (2, 1)])]
} in
let expected = {
  empty with x = mapFromSeq subi [(0, pc [EqNum 1])],
             y = mapFromSeq subi [(2, pc [EqNum 0])]
} in
utest simplifyConstraints yconstr2 with Some expected using eqc else ppc in

-- Invalid constraint because the y-value has to be negative for it to add up.
let yconstr3 = {
  empty with x = mapFromSeq subi [(0, pc [EqNum 1, EqYPlusNum (2, 2)])]
} in
utest simplifyConstraints yconstr3 with None () using eqc else ppc in

let yconstr4 = {
  empty with x = mapFromSeq subi [(0, pc [EqYPlusNum (2, 1)])]
} in
let expected = {
  empty with x = mapFromSeq subi [(0, pc [EqYPlusNum (2, 1)])],
             y = mapFromSeq subi [(2, pc [NeqNum 3])]
} in
utest simplifyConstraints yconstr4 with Some expected using eqc else ppc in

let propIneq = {
  empty with x = mapFromSeq subi [(0, pc [NeqNum 1, EqYPlusNum (0, 1)])]
} in
let expected = {
  empty with x = mapFromSeq subi [(0, pc [EqYPlusNum (0, 1)])],
             y = mapFromSeq subi [(0, pc [NeqNum 0, NeqNum 3])]
} in
utest simplifyConstraints propIneq with Some expected using eqc else ppc in

let prop = {
  empty with x = mapFromSeq subi [(0, pc [EqYPlusNum (1, 2), EqYPlusNum (2, 1)])]
} in
let expected = {
  empty with
    x = mapFromSeq subi [(0, pc [EqYPlusNum (1, 2)])],
    y = mapFromSeq subi [
      (1, pc [NeqNum 2, NeqNum 3]),
      (2, pc [EqYPlusNum (1, 1), NeqNum 3])]
} in
utest simplifyConstraints prop with Some expected using eqc else ppc in

()
