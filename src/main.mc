include "string.mc"
include "map.mc"
include "parse.mc"
include "viterbi.mc"

-- TODO:
-- kmer to unique index
-- Always 4 bases?
-- Initial probabilities?
-- What are mapped reads?

type State = {
  kmer : [a],
  layer : Int
}

let compareStates = lam s1 : State. lam s2 : State.
  let cmp = cmpString s1.kmer s2.kmer in
  if eqi cmp 0 then
    subi s1.layer s2.layer
  else cmp

let eqStates = lam s1. lam s2. eqi (compareStates s1 s2) 0

-- predecssors
-- d = 1 <- d \in {1,2}, any satisfying kmer
-- d = 2 <- d \in {1,3}, any satisfying kmer from 1
-- ...
-- d = D <- d \in {1,D}, any satisfying kmer
let pred = lam inputs. lam numLayers : Int. lam s : State.
  let layer1 = {s with layer = 1} in
  concat
    (map (lam i. {layer1 with kmer = cons i (init layer1.kmer)}) inputs)
    (if eqi s.layer numLayers then
       [{s with layer = s.layer}]
     else
       [{s with layer = addi s.layer 1}])

let _bases = "ACGT"
let _eqPreds = lam s1. lam s2.
  let s1 = sort compareStates s1 in
  let s2 = sort compareStates s2 in
  eqSeq eqStates s1 s2

utest pred _bases 3 {kmer = "AAA", layer = 1} with [
  {kmer = "AAA", layer = 1},
  {kmer = "CAA", layer = 1},
  {kmer = "GAA", layer = 1},
  {kmer = "TAA", layer = 1},
  {kmer = "AAA", layer = 2}
] using _eqPreds
utest pred _bases 3 {kmer = "AAA", layer = 2} with [
  {kmer = "AAA", layer = 1},
  {kmer = "CAA", layer = 1},
  {kmer = "GAA", layer = 1},
  {kmer = "TAA", layer = 1},
  {kmer = "AAA", layer = 3}
] using _eqPreds

recursive let powf = lam b : Float. lam e : Int.
  if eqi e 0 then 1.0
  else mulf b (powf b (subi e 1))
end

let initProbs = lam numInputs. lam s : State.
  if eqi s.layer 1 then
    divf 1.0 (powf (int2float numInputs) (length s.kmer))
  else negf (divf 1.0 0.0)

let states = lam inputs. lam kmerLength. lam numLayers.
  recursive let work = lam n.
    if eqi n 0 then [[]]
    else
      let recTails = work (subi n 1) in
      join (map (lam tail. map (lam letter. cons letter tail) inputs) recTails)
  in
  let kmers = work kmerLength in
  recursive let work2 = lam n.
    if eqi n 0 then []
    else
      let states = map (lam kmer. {kmer = kmer, layer = n}) kmers in
      concat states (work2 (subi n 1))
  in
  work2 numLayers

utest states _bases 0 1 with [{kmer = [], layer = 1}] using eqSeq eqStates
utest states "AC" 2 2
with [{kmer = "AA", layer = 1},
      {kmer = "CA", layer = 1},
      {kmer = "AC", layer = 1},
      {kmer = "CC", layer = 1},
      {kmer = "AA", layer = 2},
      {kmer = "CA", layer = 2},
      {kmer = "AC", layer = 2},
      {kmer = "CC", layer = 2}]
using (lam s1. lam s2.
         let s1 = sort compareStates s1 in
         let s2 = sort compareStates s2 in
         eqSeq eqStates s1 s2)

let stateToIndex = lam numInputs. lam baseToIndex : a -> Int. lam s : State.
  foldl
    addi
    0
    (mapi
      (lam i. lam k.
        let factor = floorfi (powf (int2float numInputs) i) in
        muli (baseToIndex k) factor)
      s.kmer)

let _bases = "AC"
let _baseToIndex = lam c.
  if eqc c 'A' then 0 else if eqc c 'C' then 1 else error (join ["Unknown input: ", [c]])
utest stateToIndex 2 _baseToIndex {kmer = "AA", layer = 1} with 0
utest stateToIndex 2 _baseToIndex {kmer = "AA", layer = 2} with 0
utest stateToIndex 2 _baseToIndex {kmer = "AC", layer = 1} with 2
utest stateToIndex 2 _baseToIndex {kmer = "CC", layer = 2} with 3

let printState : State -> String = lam s : State.
  join ["{kmer=", s.kmer, ", layer=", int2string s.layer, "}"]

let printStates = lam states : [State].
  let layer1states : [State] = filter (lam s : State. eqi s.layer 1) states in
  if null layer1states then []
  else match layer1states with [h] ++ t then
    join [h.kmer, map (lam s : State. last s.kmer) t]
  else never

mexpr

let model = parseModel (get argv 1) in
let signals = parseSignals (get argv 2) in
let bases = "ACGT" in
let inputSignal : Signal = get signals 0 in
let baseToIndex = lam input : Char.
  if eqc input 'A' then 0
  else if eqc input 'C' then 1
  else if eqc input 'G' then 2
  else if eqc input 'T' then 3
  else error (join ["Invalid input character: ", [input]])
in

let result : ViterbiResult =
  viterbi
    compareStates
    (pred bases model.dMax)
    (lam s1 : State. lam s2 : State.
      let stateIdx = stateToIndex (length bases) baseToIndex s1 in
      let baseIdx = baseToIndex (last s2.kmer) in
      get (get model.transitionProbabilities baseIdx) stateIdx)
    (initProbs (length bases))
    (states bases model.k model.dMax)
    -- model.outputProbabilities
    (lam s : State. lam i : Int.
      let stateIndex = stateToIndex (length bases) baseToIndex s in
      get (get model.observationProbabilities i) stateIndex)
    inputSignal.values
in

let lastState : State = last result.states in
utest lastState.layer with 1 in

-- printLn (join ["[\n", strJoin ",\n" (map printState result.states), "]"]);
printLn (printStates result.states);
printLn (float2string result.prob)
