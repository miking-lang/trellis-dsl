-- Performs simplification of the set constraint representation.

include "result.mc"
include "set.mc"
include "utest.mc"
include "mexpr/info.mc"

include "compile.mc"

lang TrellisConstraintSimplification = TrellisModelCompileSetConstraint
  -- Extensions of the constraint error type introduced in compile.mc
  syn ConstraintError =
  | ContradictionError Info
  | NonLiteralConstraint (Info, PredConstraint)
  | OutOfValidRange Info

  sem constraintErrorInfo =
  | ContradictionError i -> i
  | NonLiteralConstraint (i, _) -> i
  | OutOfValidRange i -> i

  sem printConstraintError =
  | ContradictionError i ->
    infoErrorString i "Found contradictory constraints"
  | NonLiteralConstraint (i, c) ->
    infoErrorString i (concat "Unsupported non-literal constraint " (printPredConstraint c))
  | OutOfValidRange i ->
    infoErrorString i "Literal equality constraint is outside range of type"

  sem eqConstraintErrorH =
  | (NonLiteralConstraint l, NonLiteralConstraint r) ->
    eqi (cmpPredConstraint l.1 r.1) 0

  -- Attempts to simplify the given constraints, producing a result which
  -- contains error if the simplification results in contradictions or
  -- violations of a valid program.
  sem simplifyConstraints : ConstraintRepr -> ConstraintResult
  sem simplifyConstraints =
  | constraints ->
    let acc = simplifyFromStateConstraints constraints in
    result.bind acc simplifyToStateConstraints

  sem simplifyFromStateConstraints : ConstraintRepr -> ConstraintResult
  sem simplifyFromStateConstraints =
  | constraints ->
    let info = constraints.info in
    let state = constraints.state in
    let simplifyConstraints = lam acc. lam idx. lam c.
      -- 1. Propagate literal constraints on the from-state to the
      --    constraints on to-state, and propagate the to-state constraints
      --    pairwise to each other as well as individually.
      let acc = propagateFromStateConstraints info state acc c in

      -- 2. Validate the literal equality constraints. The result depends on
      --    how many equality constraints we have:
      --    - If we have zero, the equal literal is -1, and all constraints
      --      are returned.
      --    - If we have one, this literal value is returned along with the
      --      remaining constraints.
      --    - If we have more than one, we have a contradiction.
      let res = validateLiteralEqualityConstraints info state idx (result.ok c) in
      match result.toOption res with Some (eqn, rest) then
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
          result.map (lam env. {env with x = mapInsert idx c env.x}) acc
        else
          -- 4. If we have a literal equality constraint, we eliminate all
          --    inequality constraints (while ensuring we have no
          --    contradiction). The result is that we only have one literal
          --    equality constraint.
          match eliminateInequalityConstraints eqn rest with Some c then
            let v = singletonConstraint (EqNum (eqn, info)) in
            result.map (lam env. {env with x = mapInsert idx v env.x}) acc
          else result.withAnnotations (result.err (ContradictionError info)) acc
      else result.withAnnotations res acc
    in
    mapFoldWithKey simplifyConstraints (result.ok constraints) constraints.x

  sem propagateFromStateConstraints : Info -> [Int] -> ConstraintResult
                                   -> Set PredConstraint -> ConstraintResult
  sem propagateFromStateConstraints info state acc =
  | constraints ->
    let isLiteralConstraint = lam c.
      match c with EqNum _ | NeqNum _ then true
      else false
    in
    let propagateLiteralConstraints = lam litConstraints. lam acc. lam c.
      match c with EqYPlusNum (yidx, n, _) then
        foldl (propagateLiteralConstraint state yidx n) acc litConstraints
      else result.withAnnotations (result.err (NonLiteralConstraint (info, c))) acc
    in
    match partition isLiteralConstraint (setToSeq constraints)
    with (literalConstraints, toStateConstraints) in

    -- 1. Propagate every literal constraint to each of the to-state components
    -- referred to in the to-state constraints.
    let acc = foldl (propagateLiteralConstraints literalConstraints) acc toStateConstraints in

    -- 2. Propagate constraints on the to-state for each pair of constraints
    -- on the from-state expressed in terms of the to-state.
    let acc = propagatePairwiseToConstraints state acc toStateConstraints in

    -- 3. Propagate constraints directly from each to-state, based on the
    -- fact that they are only valid when the corresponding x-value is
    -- within its bounds.
    foldl (propagateBoundConstraint state) acc toStateConstraints

  sem propagateLiteralConstraint : [Int] -> Int -> Int -> ConstraintResult
                                -> PredConstraint -> ConstraintResult
  sem propagateLiteralConstraint state yidx yn acc =
  | EqNum (n, info) ->
    let ymaxval = get state yidx in
    let np = subi n yn in
    if and (geqi np 0) (lti np ymaxval) then
      let yconstraint = singletonConstraint (EqNum (np, info)) in
      result.map (lam env. {env with y = mapInsertWith setUnion yidx yconstraint env.y}) acc
    else result.withAnnotations (result.err (OutOfValidRange info)) acc
  | NeqNum (n, info) ->
    let np = subi n yn in
    let yconstraint = singletonConstraint (NeqNum (np, info)) in
    result.map (lam env. {env with y = mapInsertWith setUnion yidx yconstraint env.y}) acc

  sem propagatePairwiseToConstraints : [Int] -> ConstraintResult
                                    -> [PredConstraint] -> ConstraintResult
  sem propagatePairwiseToConstraints state acc =
  | toConstraints ->
    let propagateConstraints = lam acc. lam idxc.
      match idxc with (index, c) in
      -- NOTE(larshum, 2024-04-23): In the below line, we pick all constraints
      -- beyond the current one in the sequence. This is to go through all
      -- pairs of constraints.
      let rhs = subsequence toConstraints (addi index 1) (length toConstraints) in
      foldl (lam acc. lam c2. propagateConstraint state acc (c, c2)) acc rhs
    in
    let indexedConstraints = mapi (lam idx. lam x. (idx, x)) toConstraints in
    foldl propagateConstraints acc indexedConstraints

  sem propagateConstraint : [Int] -> ConstraintResult
                         -> (PredConstraint, PredConstraint)
                         -> ConstraintResult
  sem propagateConstraint state acc =
  | (EqYPlusNum (lidx, ln, linfo), EqYPlusNum (ridx, rn, rinfo)) ->
    let n = subi rn ln in
    match
      if lti n 0 then (negi n, lidx, ridx)
      else (n, ridx, lidx)
    with (n, srcIdx, dstIdx) in
    let ymax = get state srcIdx in
    let info = mergeInfo linfo rinfo in
    if and (geqi n 0) (lti n ymax) then
      let c = singletonConstraint (EqYPlusNum (srcIdx, n, info)) in
      result.map (lam env. {env with y = mapInsertWith setUnion dstIdx c env.y}) acc
    else result.withAnnotations (result.err (OutOfValidRange info)) acc
  | (l, r) ->
    error (join [
      "Unexpected constraints: ", printPredConstraint l, " and ",
      printPredConstraint r
    ])

  sem propagateBoundConstraint : [Int] -> ConstraintResult -> PredConstraint
                              -> ConstraintResult
  sem propagateBoundConstraint state acc =
  | EqYPlusNum (yidx, n, info) ->
    let maxv = get state yidx in
    let invalidValues =
      if lti n 0 then create n (lam i. i)
      else create n (lam i. subi (subi maxv i) 1)
    in
    let c = setOfSeq cmpPredConstraint (map (lam n. NeqNum (n, info)) invalidValues) in
    result.map (lam env. {env with y = mapInsertWith setUnion yidx c env.y}) acc
  | c ->
    error (concat "Unexpected constraint on to-state: " (printPredConstraint c))

  sem validateLiteralEqualityConstraints : Info -> [Int] -> Int
                                        -> Result () ConstraintError (Set PredConstraint)
                                        -> Result () ConstraintError (Int, Set PredConstraint)
  sem validateLiteralEqualityConstraints info state idx =
  | constraints ->
    let eqLit = lam c.
      match c with EqNum n then Some n else None ()
    in
    let eqc = result.map (lam c. mapOption eqLit (setToSeq c)) constraints in
    -- NOTE(larshum, 2024-04-23): If we have more than one literal equality
    -- constraint, this is a contradiction. We also have a contradiction if the
    -- literal value is outside of its valid range.
    switch result.toOption eqc
    case Some [] then result.map (lam c. (-1, c)) constraints
    case Some [(n, ninfo)] then
      let maxval = get state idx in
      if and (geqi n 0) (lti n maxval) then
        result.map (lam c. (n, setRemove (EqNum (n, ninfo)) c)) constraints
      else
        -- NOTE(larshum, 2024-04-24): We perform the below operation to get the
        -- correct return type.
        let c = result.map (lam c. (0, c)) constraints in
        result.withAnnotations (result.err (OutOfValidRange ninfo)) c
    case Some _ then
      let c = result.map (lam c. (0, c)) constraints in
      result.withAnnotations (result.err (ContradictionError info)) c
    case _ then
      let c = result.map (lam c. (0, c)) constraints in
      result.withAnnotations eqc c
    end

  sem eliminateInequalityConstraints : Int -> Set PredConstraint -> Option (Set PredConstraint)
  sem eliminateInequalityConstraints eqn =
  | constraints ->
    let neqLitConstraint = lam c.
      match c with NeqNum _ then true else false
    in
    let compareInequality = lam c.
      match c with NeqNum (n, _) then neqi n eqn
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
      match c with NeqNum (n, _) then or (lti n 0) (geqi n maxv) else false
    in
    mapFilterWithKey (lam c. lam. not (isContradictoryInequality c)) constraints

  sem simplifyToStateConstraints : ConstraintRepr -> ConstraintResult
  sem simplifyToStateConstraints =
  | constraints ->
    let info = constraints.info in
    let state = constraints.state in
    let simplifyConstraints = lam acc. lam idx. lam c.
      -- 1. Remove inequallity constraints that are contradictory due to being
      --    negative or beyond the range of the type.
      let c =
        result.map
          (lam constraints.
            let maxv = get constraints.state idx in
            removeContradictoryInequalityConstraints maxv c)
          acc
      in

      -- 2. Validate the literal equality constraints (as for the from-state).
      let res = validateLiteralEqualityConstraints info state idx c in
      match result.toOption res with Some (eqn, rest) then
        if eqi eqn -1 then
          result.map (lam c. {c with y = mapInsert idx rest c.y}) acc
        else
          -- 3. If we have a literal equality constraint, we remove all
          --    inequality constraints and ensure these do not contradict the
          --    equality constraint.
          match eliminateInequalityConstraints eqn rest with Some c then
            let v = setInsert (EqNum (eqn, info)) c in
            result.map (lam c. {c with y = mapInsert idx v c.y}) acc
          else result.withAnnotations (result.err (ContradictionError info)) acc
      else result.withAnnotations res acc
    in
    mapFoldWithKey simplifyConstraints (result.ok constraints) constraints.y
end

lang TestLang = TrellisConstraintSimplification + ConstraintTestLang
end

mexpr

use TestLang in

let pc = setOfSeq cmpPredConstraint in

-- NOTE(larshum, 2024-04-24): The empty constraint environment, which has no
-- constraints on the from-state or the to-state, represents a set constraint
-- that describes all possible transitions between pairs of states.
let empty = {
  state = [4, 4, 4, 16],
  x = mapEmpty subi,
  y = mapEmpty subi,
  info = NoInfo ()
} in
utest simplifyConstraints empty with result.ok empty using eqc else ppc in

let eqn_ = lam n. EqNum (n, NoInfo ()) in
let neqn_ = lam n. NeqNum (n, NoInfo ()) in
let eqypn_ = lam yidx. lam n. EqYPlusNum (yidx, n, NoInfo ()) in
let valid = {
  empty with x = mapFromSeq subi [(0, pc [eqn_ 1])]
} in
utest simplifyConstraints valid with result.ok valid using eqc else ppc in

let inconsistent = {
  empty with x = mapFromSeq subi [(0, pc [eqn_ 1, eqn_ 2])]
} in
let expected = result.err (ContradictionError (NoInfo ())) in
utest simplifyConstraints inconsistent with expected using eqc else ppc in

let xconstr = {
  empty with x = mapFromSeq subi [(0, pc [eqn_ 1, neqn_ 2])]
} in
utest simplifyConstraints xconstr with result.ok valid using eqc else ppc in

let manyneqelim = {
  empty with x = mapFromSeq subi [(3, pc [eqn_ 1, neqn_ 5, neqn_ 7, neqn_ 4, neqn_ 9])]
} in
let expected = {
  empty with x = mapFromSeq subi [(3, pc [eqn_ 1])]
} in
utest simplifyConstraints manyneqelim with result.ok expected using eqc else ppc in

let yconstr = {
  empty with x = mapFromSeq subi [(0, pc [eqn_ 1, eqypn_ 2 0])]
} in
let expected = {
  empty with x = mapFromSeq subi [(0, pc [eqn_ 1])],
             y = mapFromSeq subi [(2, pc [eqn_ 1])]
} in
utest simplifyConstraints yconstr with result.ok expected using eqc else ppc in

let yconstr2 = {
  empty with x = mapFromSeq subi [(0, pc [eqn_ 1, eqypn_ 2 1])]
} in
let expected = {
  empty with x = mapFromSeq subi [(0, pc [eqn_ 1])],
             y = mapFromSeq subi [(2, pc [eqn_ 0])]
} in
utest simplifyConstraints yconstr2 with result.ok expected using eqc else ppc in

-- Invalid constraint because the y-value has to be negative for it to add up.
let yconstr3 = {
  empty with x = mapFromSeq subi [(0, pc [eqn_ 1, eqypn_ 2 2])]
} in
let expected = result.err (OutOfValidRange (NoInfo ())) in
utest simplifyConstraints yconstr3 with expected using eqc else ppc in

let yconstr4 = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 2 1])]
} in
let expected = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 2 1])],
             y = mapFromSeq subi [(2, pc [neqn_ 3])]
} in
utest simplifyConstraints yconstr4 with result.ok expected using eqc else ppc in

let propIneq = {
  empty with x = mapFromSeq subi [(0, pc [neqn_ 1, eqypn_ 0 1])]
} in
let expected = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 1])],
             y = mapFromSeq subi [(0, pc [neqn_ 0, neqn_ 3])]
} in
utest simplifyConstraints propIneq with result.ok expected using eqc else ppc in

let prop = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 1 2, eqypn_ 2 1])]
} in
let expected = {
  empty with
    x = mapFromSeq subi [(0, pc [eqypn_ 1 2])],
    y = mapFromSeq subi [
      (1, pc [neqn_ 2, neqn_ 3]),
      (2, pc [eqypn_ 1 1, neqn_ 3])]
} in
utest simplifyConstraints prop with result.ok expected using eqc else ppc in

let lhs = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 1])]
} in
let lhsExpected = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 1])],
             y = mapFromSeq subi [(0, pc [neqn_ 3])]
} in
utest simplifyConstraints lhs with result.ok lhsExpected using eqc else ppc in

let rhs = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 2])]
} in
let rhsExpected = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 2])],
             y = mapFromSeq subi [(0, pc [neqn_ 3, neqn_ 2])]
} in
utest simplifyConstraints rhs with result.ok rhsExpected using eqc else ppc in

let lhs = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 1, eqypn_ 1 1])]
} in
let lhsExpected = {
  empty with x = mapFromSeq subi [(0, pc [eqypn_ 0 1])],
             y = mapFromSeq subi [(0, pc [eqypn_ 1 0, neqn_ 3]), (1, pc [neqn_ 3])]
} in
utest simplifyConstraints lhs with result.ok lhsExpected using eqc else ppc in

let rhs = {
  empty with y = mapFromSeq subi [(0, pc [neqn_ 2]), (1, pc [eqn_ 2])]
} in
utest simplifyConstraints rhs with result.ok rhs using eqc else ppc in

()
