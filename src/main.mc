include "string.mc"
include "map.mc"

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
let pred = lam inputs : [a]. lam numLayers : Int. lam s : State.
  let layer1 = {s with layer = 1} in
  concat
    (map (lam i. {layer1 with kmer = cons i (init layer1.kmer)}) inputs)
    (if eqi s.layer numLayers then
       [{s with layer = s.layer}]
     else
       [{s with layer = addi s.layer 1}])

let _inputs = ['A','C','G','T']
let _eqPreds = lam s1. lam s2.
  let s1 = sort compareStates s1 in
  let s2 = sort compareStates s2 in
  eqSeq eqStates s1 s2

utest pred _inputs 3 {kmer = ['A','A','A'], layer = 1} with [
  {kmer = ['A','A','A'], layer = 1},
  {kmer = ['C','A','A'], layer = 1},
  {kmer = ['G','A','A'], layer = 1},
  {kmer = ['T','A','A'], layer = 1},
  {kmer = ['A','A','A'], layer = 2}
] using _eqPreds
utest pred _inputs 3 {kmer = ['A','A','A'], layer = 2} with [
  {kmer = ['A','A','A'], layer = 1},
  {kmer = ['C','A','A'], layer = 1},
  {kmer = ['G','A','A'], layer = 1},
  {kmer = ['T','A','A'], layer = 1},
  {kmer = ['A','A','A'], layer = 3}
] using _eqPreds

recursive let powf = lam b : Float. lam e : Int.
  if eqi e 0 then 1.0
  else mulf b (powf b (subi e 1))
end

let initProbs = lam inputs. lam s : State.
  if eqi s.layer 1 then
    divf 1.0 (powf (length inputs) (length s.kmer))
  else 0.0

let states = lam inputs. lam numLayers.
  recursive let work = lam n.
    if eqi n 0 then [[]]
    else
      let recTails = work (subi n 1) in
      join (map (lam tail. map (lam letter. cons letter tail) inputs) recTails)
  in work numLayers

-- viterbi
--  compareStates : State -> State -> Int.
--  predecessors : State -> [State].
--  transitionProb : State -> State -> LogProb.
--  initProbs : State -> LogProb.
--  states : [State].
--  outputProb : State -> a -> LogProb.
--  inputs : [a].
