include "ast.mc"
include "constant-fold.mc"
include "encode.mc"
include "pprint.mc"
include "../trellis-common.mc"

lang TrellisWritePredecessors
  -- Writes the predecessors to a file
  sem writePredecessors : String -> [[Int]] -> ()
  sem writePredecessors outputDir =
  | preds ->
    let file = join [outputDir, "/", predecessorsFileName] in
    writeFile file (strJoin "\n" (map (lam p. strJoin " " (map int2string p)) preds))
end

lang TrellisPredecessors =
  TrellisModelAst + TrellisEncode + TrellisConstantFold +
  TrellisWritePredecessors

  -- Computes the set of predecessors of each task of a given model. The result
  -- is a nested sequence, where each outer index denotes the state and the
  -- corresponding sequence denotes its predecessors.
  sem computePredecessors : TModel -> [[Int]]
  sem computePredecessors =
  | model ->
    computePredecessorsCases model.stateType model.transition.cases

  sem computePredecessorsCases : TType -> [Case] -> [[Int]]
  sem computePredecessorsCases stateType =
  | cases ->
    let conds = map (lam c. c.cond) cases in
    computePredecessorsConds stateType conds

  sem computePredecessorsConds : TType -> [TSet] -> [[Int]]
  sem computePredecessorsConds stateType =
  | conditions ->
    let cardinality = cardinalityType stateType in
    create cardinality (lam i.
      foldl
        (lam acc. lam j.
          if isPredecessor stateType conditions j i then
            snoc acc j
          else acc)
        [] (create cardinality (lam j. j)))

  sem isPredecessor : TType -> [TSet] -> Int -> Int -> Bool
  sem isPredecessor stateType conditions from =
  | to -> any (isSatisfied stateType from to) conditions

  sem isSatisfied : TType -> Int -> Int -> TSet -> Bool
  sem isSatisfied stateType from to =
  | SAll _ -> true
  | STransitionBuilder t ->
    let subMap = mapFromSeq nameCmp [(t.x, from), (t.y, to)] in
    let conds = map (substituteVariables subMap) t.conds in
    let conds = map constantFold conds in
    forAll isTrue conds
  | STransitionLiteral _ ->
    false
  | SValueBuilder {info = info} | SValueLiteral {info = info} ->
    errorSingle [info]
      "Transition probability function cannot use sets of states in conditions"

  sem substituteVariables : Map Name Int -> TExpr -> TExpr
  sem substituteVariables subMap =
  | EVar t ->
    match mapLookup t.id subMap with Some n then
      EInt {i = n, ty = t.ty, info = t.info}
    else errorSingle [t.info] "Failed to substitute variable"
  | e -> smapTExprTExpr (substituteVariables subMap) e

  sem isTrue : TExpr -> Bool
  sem isTrue =
  | EBool {b = b} -> b
  | _ -> false
end

lang TestLang = TrellisPredecessors + TrellisModelPrettyPrint
end

mexpr

use TestLang in

let testPreds = lam ty. lam conds.
  let conds = map (smapTSetTExpr (encodeStateOperationsExpr false)) conds in
  computePredecessorsConds ty conds
in

let i = trellisInfo "trellis-predecessors" in

let c1 = SAll {info = i} in
let ty1 = TBool {info = i} in
utest testPreds ty1 [c1] with [[0,1],[0,1]] in

let x = nameSym "x" in
let y = nameSym "y" in
let ty2 = TInt {bounds = Some (2, 7), info = i} in
let prevStatePred = EBinOp {
  op = OEq (), lhs = EVar {id = y, ty = ty2, info = i},
  rhs = EBinOp {
    op = OAdd (), lhs = EVar {id = x, ty = ty2, info = i},
    rhs = EInt {i = 1, ty = ty2, info = i},
    ty = ty2, info = i
  },
  ty = ty2, info = i
} in
let c2 = STransitionBuilder {x = x, y = y, conds = [prevStatePred], info = i} in
utest testPreds ty2 [c2] with [[],[0],[1],[2],[3],[4]] in
utest testPreds ty2 [c2,c1] with create 6 (lam. [0,1,2,3,4,5]) in

-- The K-mer example with K=1 (to lower the number of states)
let kmer = TInt {bounds = Some (0, 3), info = i} in
let duration = TInt {bounds = Some (1, 16), info = i} in
let stateTy = TTuple {tys = [kmer, duration], info = i} in
let var = lam x. lam ty. EVar {id = x, ty = ty, info = i} in
let int = lam n. EInt {i = n, ty = TInt {bounds = None (), info = i}, info = i} in
let bop = lam op. lam l. lam r. lam ty.
  EBinOp { op = op, lhs = l, rhs = r, ty = ty, info = i }
in
let eq = lam l. lam r. bop (OEq ()) l r (TBool {info = i}) in
let proj = lam x. lam n. lam ty.
  ESlice { target = var x stateTy, lo = n, hi = n, ty = ty, info = i }
in
let maxDuration = lam x.
  eq (proj x 1 duration) (int 16)
in
let lhsEq1 = eq (proj x 1 duration) (int 1) in
let eqKmer = eq (proj x 0 kmer) (proj y 0 kmer) in
let c1 = STransitionBuilder {x = x, y = y, conds = [lhsEq1], info = i} in
let c2 = STransitionBuilder {
  x = x, y = y, conds = [eqKmer, maxDuration x, maxDuration y], info = i
} in
let c3 = STransitionBuilder {
  x = x, y = y,
  conds = [
    eqKmer, maxDuration x,
    eq (proj y 1 duration) (bop (OSub ()) (int 16) (int 1) duration)],
  info = i
} in
let c4 = STransitionBuilder {
  x = x, y = y,
  conds = [
    eqKmer,
    eq (proj y 1 duration) (bop (OSub ()) (proj x 1 duration) (int 1) duration)
  ],
  info = i
} in
let ppset = lam s. match pprintTrellisSet pprintEnvEmpty s with (_, s) in s in
let preds = lam i.
  let kmer = divi i 16 in
  let duration = modi i 16 in
  let durPred =
    if eqi duration 15 then i
    else addi i 1
  in
  let kmerPreds = create 4 (lam j. muli j 16) in
  sort subi (cons durPred kmerPreds)
in
utest testPreds stateTy [c1,c2,c3,c4]
with create (cardinalityType stateTy) preds in

()
