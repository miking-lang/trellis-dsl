include "seq.mc"
include "map.mc"
include "math.mc"

let probMul : Prob -> Prob -> Prob = mulf
let probAdd : Prob -> Prob -> Prob = addf
let probDiv : Prob -> Prob -> Prob = divf

let zipWith3 : (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
  = lam f.
    recursive let work = lam as. lam bs. lam cs.
      match (as, bs, cs) with ([a] ++ as, [b] ++ bs, [c] ++ cs) then
        cons (f a b c) (work as bs cs)
      else []
    in work

let scanr : (a -> b -> b) -> b -> [a] -> b
  = lam f. lam acc.
    recursive let work = lam as.
      match as with [] then (acc, []) else
      match as with [a] ++ as then
        match work as with (acc, nexts) then
          let acc = f a acc in
          (acc, cons acc nexts)
        else never
      else never
    in lam as. (work as).1

let forwardBackward = -- ... -> { alphaHat : [Map State Prob]
                             -- , betaHat : [Map State Prob]
                             -- , c : [Prob]
                             -- }
  lam compareStates : State -> State -> Int.
  lam predecessors : State -> [State].
  lam successors : State -> [State].
  lam transitionProb : State -> State -> Prob.
  lam initProbs : State -> Prob.
  lam states : [State].
  lam outputProb : State -> a -> Prob.
  lam inputs : [a].
  let stateMap = mapFromList compareStates (map (lam s. (s, ())) states) in
  recursive
    let forward = -- ... -> {alphaHat : [Map State Prob], c : [Prob]}
      lam alphaHat : [Map State Prob].
      lam c : [Prob].
      lam inputs.
        match inputs with [] then
          {alphaHat = alphaHat, c = c}
        else match inputs with [x] ++ inputs then
          let alphaHatPrev = last alphaHat in
          let alphaTemp =
            mapMapWithKey
              (lam state. lam.
                 let sum = foldl
                   (lam acc. lam s.
                      probAdd acc (probMul (transitionProb s state)
                                           (mapFindWithExn s alphaHatPrev)))
                   0.0 (predecessors state)
                 in probMul sum (outputProb state x))
              stateMap
          in
          let cNew = mapFoldWithKey (lam acc. lam. lam prob. probAdd acc prob)
                                    0.0 alphaTemp in
          let alphaHatNew = mapMap (lam prob. probDiv prob cNew) alphaTemp in
          forward (snoc alphaHat alphaHatNew) (snoc c cNew) inputs
        else never
    let backward = -- ... -> betaHat : [Map State Prob]
      lam c : Prob.
      lam input : a.
      lam acc : [Map State Prob].
      let betaHatPrev = head acc in
      let betaHatNew = mapMapWithKey
        (lam stateFrom. lam.
           probDiv
             (foldl (lam acc. lam stateTo.
                probAdd acc
                  (probMul (probMul (transitionProb stateFrom stateTo)
                                    (outputProb stateTo input))
                           (mapFindWithExn stateTo betaHatPrev)))
                0.0 (successors stateFrom))
             c)
        stateMap in
      cons betaHatNew acc
  in
  match inputs with [] then
    {alphaHat = [], betaHat = [], c = []}
  else match inputs with [x] ++ inputs then
    let alphaTempFirst = mapMapWithKey (lam state. lam.
        probMul (initProbs state) (outputProb state x)) stateMap in
    let cFirst = mapFoldWithKey (lam acc. lam. lam prob. probAdd acc prob) 0.0
                 alphaTempFirst in
    let alphaHatFirst = mapMap (lam prob. probDiv prob cFirst) alphaTempFirst in
    match forward [alphaHatFirst] [cFirst] inputs
    with {c = c, alphaHat = alphaHat} then
      let betaHatLast = mapMapWithKey (lam. lam. probDiv 1.0 (last c)) stateMap in
      let betaHat = foldr (lam f. lam acc. f acc) [betaHatLast] (zipWith backward (init c) inputs) in
      {alphaHat = alphaHat, betaHat = betaHat, c = c}
    else never
  else never


mexpr

let eqProb = lam delta. lam l. lam r.
  (ltf (absf (subf l r)) delta)
in

let delta = 1e-2 in

-- From https://en.wikipedia.org/wiki/Forward%E2%80%93backward_algorithm#Example
let predecessors = [[0, 1], [0, 1]] in
let successors = [[0, 1], [0, 1]] in
let transitionProbs = [
  [0.7, 0.3],
  [0.3, 0.7]
] in
let initProbs = [0.5, 0.5] in
let states = [0, 1] in
let outputProbs = [
  [(1, 0.9), (2, 0.1)],
  [(1, 0.2), (2, 0.8)]
] in
let outputProb = lam state. lam v.
  match find (lam t. eqi v t.0) (get outputProbs state) with Some t then
    t.1
  else error (join ["No key '", v, "' found"])
in
let result = forwardBackward
  subi
  (lam state. get predecessors state)
  (lam state. get successors state)
  (lam fromState. lam toState. get (get transitionProbs fromState) toState)
  (lam state. get initProbs state)
  states
  outputProb
  [1, 1, 2, 1, 1]
in

match result with {alphaHat = a, betaHat = b, c = c} then
  let gamma = zipWith3
      (lam x. lam y. lam z.
        mapMapWithKey (lam state. lam x.
          probMul (probMul x (mapFindWithExn state y)) z)
          x)
      a b c in

  let normalize = lam values.
    let sum = mapFoldWithKey (lam acc. lam. lam prob. probAdd acc prob) 0.0 values
    in mapMap (lam v. probDiv v sum) values
  in

  utest map mapBindings a with [
    [(0, 0.8182), (1, 0.1818)],
    [(0, 0.8834), (1, 0.1166)],
    [(0, 0.1907), (1, 0.8093)],
    [(0, 0.7308), (1, 0.2692)],
    [(0, 0.8673), (1, 0.1327)]
  ] using eqSeq (eqSeq (lam l. lam r. and (eqi l.0 r.0) (eqProb delta l.1 r.1))) in
  utest map mapBindings (map normalize b) with [
    [(0, 0.5923), (1, 0.4077)],
    [(0, 0.3763), (1, 0.6237)],
    [(0, 0.6533), (1, 0.3467)],
    [(0, 0.6273), (1, 0.3727)],
    [(0, 0.5000), (1, 0.5000)]
  ] using eqSeq (eqSeq (lam l. lam r. and (eqi l.0 r.0) (eqProb delta l.1 r.1))) in
  utest map mapBindings gamma with [
    [(0, 0.8673), (1, 0.1327)], -- f(0:1) b(1:5)
    [(0, 0.8204), (1, 0.1796)], -- f(0:2) b(2:5)
    [(0, 0.3075), (1, 0.6925)], -- f(0:3) b(3:5)
    [(0, 0.8204), (1, 0.1796)], -- f(0:4) b(4:5)
    [(0, 0.8673), (1, 0.1327)]  -- f(0:5) b(5:5)
  ] using eqSeq (eqSeq (lam l. lam r. and (eqi l.0 r.0) (eqProb delta l.1 r.1))) in
  utest c with map (lam x. divf 1.0 x) [1.818, 1.565, 2.92, 2.158, 1.627]
  using eqSeq (eqProb delta) in
  ()
else never
