include "math.mc"
include "string.mc"

let mapInit : (k -> k -> Int) -> [k] -> (k -> v) -> Map k v = lam compare. lam keys. lam f.
  foldl (lam acc. lam k. mapInsert k (f k) acc) (mapEmpty compare) keys

let probMul : LogProb -> LogProb -> LogProb = addf

let maxBy : (a -> LogProb) -> [a] -> Option a = lam f.
  recursive let work = lam maxFA. lam maxA. lam as.
    match as with [] then Some maxA else
    match as with [a] ++ as then
      let fa = f a in
      if (gtf fa maxFA)
      then work fa a as
      else work maxFA maxA as
    else never
  in lam as. match as with [] then None () else
    match as with [a] ++ as then
    work (f a) a as
    else never

let headExc : [a] -> a = lam as.
  match as with [a] ++ _ then a else
  error "Empty list in headExc"

let mapMaxBy : (a -> LogProb) -> Map k a -> Option k = lam f. lam m.
  optionMap (lam x. x.0) (maxBy (lam binding. f binding.1) (mapBindings m))
let mapMaxByExc : (a -> LogProb) -> Map k a -> Option k = lam f. lam m.
  match mapMaxBy f m with Some x then x
  else let _ = dprint (mapBindings m) in error "Empty map in mapMaxByExc"

let viterbi = -- ... -> {states : [State], prob : LogProb}
  lam compareStates : State -> State -> Int.
  lam predecessors : State -> [State].
  lam transitionProb : State -> State -> LogProb.
  lam initProbs : State -> LogProb.
  lam states : [State].
  lam outputProb : State -> a -> LogProb.
  lam inputs : [a].
  match inputs with [x] ++ inputs then
  let chi1 = mapInit compareStates states
    (lam state. probMul (initProbs state) (outputProb state x)) in
  let arbitraryState = headExc states in
  recursive
    let forward = -- ... -> {chi : Map State LogProb, zeta : [Map State State]}
      lam chi : Map State LogProb.
      lam zeta : [Map State State].
      lam inputs : [a].
        match inputs with [] then {chi = chi, zeta = zeta} else
        match inputs with [x] ++ inputs then
          let logProbFrom : State -> State -> LogProb =
            lam state. lam pre. probMul (mapFind pre chi) (transitionProb pre state) in
          let newZeta : Map State State = mapInit compareStates states
            (lam state. optionGetOr arbitraryState (maxBy (logProbFrom state) (predecessors state))) in
          let newChi = mapMapWithKey (lam state. lam pre. probMul (logProbFrom state pre) (outputProb state x)) newZeta in
          forward newChi (snoc zeta newZeta) inputs
        else never
    let backwardStep =
      lam acc : [State].
      lam zeta : [Map State State].
      match zeta with zeta ++ [here] then
        backwardStep (cons (mapFind (headExc acc) here) acc) zeta
      else acc
  in
  match forward chi1 [] inputs with {chi = chi, zeta = zeta} then
    let lastState = mapMaxByExc identity chi in
    let logprob = mapFind lastState chi in
    {prob = logprob, states = backwardStep [lastState] zeta}
  else never else never

mexpr

let compareViterbiResult = lam delta. lam l. lam r.
  match l with {states = lstates, prob = lprob} then
    match r with {states = rstates, prob = rprob} then
      and (all (lam b. b) (zipWith eqi lstates rstates))
          (ltf (absf (subf lprob rprob)) delta)
    else never
  else never
in

let delta = 1e-2 in

-- Example adapted from
-- https://personal.utdallas.edu/~prr105020/biol6385/2019/lecture/lecture12_Viterbi_handout.pdf
let predecessors = [[0, 1], [0, 1]] in
let transitionProbs = [[negf 1.0, negf 1.0], [negf 1.322, negf 0.737]] in
let initProbs = [negf 1.0, negf 1.0] in
let states = [0, 1] in
let outputProbs = [
  [('A', negf 2.322), ('C', negf 1.737), ('G', negf 1.737), ('T', negf 2.322)],
  [('A', negf 1.737), ('C', negf 2.322), ('G', negf 2.322), ('T', negf 1.737)]
] in
let outputProb = lam state. lam v.
  match find (lam t. eqc v t.0) (get outputProbs state) with Some t then
    t.1
  else error (join ["No key '", v "' found"])
in
let inputs = ['G', 'G', 'C', 'A', 'C', 'T', 'G', 'A', 'A'] in
let mostProbableSequence =
  viterbi
    (lam state1. lam state2. subi state1 state2)
    (lam state. get predecessors state)
    (lam fromState. lam toState. get (get transitionProbs fromState) toState)
    (lam state. get initProbs state)
    states outputProb inputs
in
let expected = {prob = negf 24.49, states = [0, 0, 0, 1, 1, 1, 1, 1, 1]} in
utest mostProbableSequence with expected using compareViterbiResult delta in

-- Example adapted from https://www.pythonpool.com/viterbi-algorithm-python/
let predecessors = [[0, 1], [0, 1]] in
let transitionProbs = [[negf 0.515, negf 1.737], [negf 1.322, negf 0.737]] in
let initProbs = [negf 0.737, negf 1.322] in
let states = [0, 1] in
let outputProbs = [
  [("normal", negf 1.0), ("cold", negf 1.322), ("dizzy", negf 3.322)],
  [("normal", negf 3.322), ("cold", negf 1.737), ("dizzy", negf 0.737)]
] in
let outputProb = lam state. lam v.
  match find (lam t. eqString v t.0) (get outputProbs state) with Some t then
    t.1
  else error (join ["No key '", v, "' found"])
in
let inputs = ["normal", "cold", "dizzy"] in
let mostProbableSequence =
  viterbi
    (lam state1. lam state2. subi state1 state2)
    (lam state. get predecessors state)
    (lam fromState. lam toState. get (get transitionProbs fromState) toState)
    (lam state. get initProbs state)
    states outputProb inputs
in
let expected = {prob = negf 6.047, states = [0, 0, 1]} in
utest mostProbableSequence with expected using compareViterbiResult delta in

()
