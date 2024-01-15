
-----------------------------------
-- GENERATED INITIALIZATION CODE --
-----------------------------------

module state = i16
module obs = i8
module prob = f32
type state_t = state.t
type obs_t = obs.t
type prob_t = prob.t

-- NOTE: similar to Slack-example, but using a 3mer model
let nstates : i64 = 1024

-----------------------------------
-- NATIVE VITERBI IMPLEMENTATION --
-----------------------------------

type forw_res [n][m] = {chi : [n]prob_t, zeta : [m][n]state_t}

let max_state (f : state_t -> prob_t) (s : []state_t) : state_t =
  let cmp = \acc x -> if f acc > f x then acc else x in
  foldl cmp s[0] s[1:]

let max_index_by_state (s : []prob_t) : i64 =
  let cmp = \a b -> if a.1 > b.1 then a else b in
  let is = map (\i -> (i, s[i])) (indices s) in
  (reduce cmp is[0] is[1:]).0

let viterbi_forward [m] (predecessors : [nstates][]state_t) (transp : state_t -> state_t -> prob_t)
                        (outp : state_t -> obs_t -> prob_t) (signal : [m]obs_t)
                        (chi1 : [nstates]prob_t) : forw_res[nstates][m] =
  let zeta = tabulate m (\_ -> tabulate nstates (\_ -> state.i32 0)) in
  loop {chi, zeta} = {chi = chi1, zeta = zeta} for i < m do
    let x = signal[i] in
    let log_prob_from (s : state_t) (pre : state_t) : prob_t =
      if pre >= 0 then chi[state.to_i64 pre] + transp pre s
      else -prob.inf
    in
    let new_zeta = tabulate nstates (\s -> max_state (\p -> log_prob_from (state.i64 s) p) predecessors[s]) in
    let new_chi : [nstates]prob_t =
      map2 (\s pre -> log_prob_from (state.i64 s) pre + outp (state.i64 s) x) (indices new_zeta) new_zeta
    in
    {chi = new_chi, zeta = zeta with [i] = new_zeta}

let viterbi_backward [m] (s_last : state_t) (zeta : [m][nstates]state_t) : [1+m]state_t =
  let acc = [s_last] ++ tabulate m (\_ -> state.i32 0) in
  loop acc for i < m do
    acc with [i+1] = zeta[i][state.to_i64 acc[i]]

let main_viterbi [m] (predecessors : [nstates][]state_t) (transp : state_t -> state_t -> prob_t)
                     (initp : state_t -> prob_t) (outp : state_t -> obs_t -> prob_t)
                     (signal : [m]obs_t) : [m]state_t =
  let x = signal[0] in
  let rest = signal[1:m] in
  let chi1 = tabulate nstates (\s -> initp (state.i64 s) + outp (state.i64 s) x) in
  let r = viterbi_forward predecessors transp outp rest chi1 in
  match r
  case {chi = chi, zeta = zeta} ->
    let sLast = max_index_by_state chi in
    reverse (viterbi_backward (state.i64 sLast) (reverse zeta)) :> [m]state_t

--------------------
-- GENERATED CODE --
--------------------

-- Checks whether a pair of states belong to a particular set of transitions
let in_inter (x : state_t) (y : state_t) : bool =
  (x & 15) + 1 == 1 && ((x >> 4) & 0xFF) == ((y >> 6) & 0xFF)

-- Similar to the 'in_inter' function, but for 3mers
let in_inter_3mer (x : state_t) (y : state_t) : bool =
  (x & 15) + 1 == 1 && ((x >> 4) & 0xF) == y >> 6

let in_max (x : state_t) (y : state_t) : bool =
  x >> 4 == y >> 4 && (x & 15) == 15 && (y & 15) == 15

let in_from_max (x : state_t) (y : state_t) : bool =
  x >> 4 == y >> 4 && (x & 15) == 15 && (y & 15) == 14

let in_down (x : state_t) (y : state_t) : bool =
  x >> 4 == y >> 4 && (x & 15) == (y & 15) + 1

-- Computes the probability of the output, initial, and transition
-- probabilities based on the definitions in the automaton.
let output_probability (table_outputProb : [64][101]prob_t) (x : state_t)
                       (output : obs_t) : prob_t =
  table_outputProb[x >> 4][output]

let initial_probability (table_initialProb : [64][16]prob_t) (x : state_t) : prob_t =
  table_initialProb[x >> 4][x & 15]

let transition_probability
  (table_trans1 : [64][64]prob_t) (table_trans2 : [16]prob_t) (table_gamma : prob_t)
  (x : state_t) (y : state_t) : prob_t =

  if in_inter_3mer x y then table_trans1[x >> 4][y >> 4] + table_trans2[y & 15]
  else if in_max x y then table_gamma
  else if in_from_max x y then prob.log (prob.exp 1.0 - prob.exp table_gamma)
  else if in_down x y then prob.log 1.0
  else -prob.inf

-- 1. Count the number of predecessors of each state
-- 2. Compute the maximum number of predecessors
-- 3. Generate an array of predecessors for each state, padded with -1 to
--    indicate a non-existent predecessor.
let find_predecessors (transp : state_t -> state_t -> prob_t) (nstates : i64) : [nstates][]state_t =
  let pred_count =
    map
      (\s ->
        -- inter
        let count = loop count = 0 for a < 4 do
          let p = (a << 8) | (((s >> 6) & 0xF) << 4) | 0 in
          if transp p s != prob.inf then count + 1 else count
        in
        -- max
        let count =
          if s & 15 == 15 then
            let p = s in
            if transp p s != prob.inf then count + 1 else count
          else count
        in
        -- from_max
        let count =
          if s & 15 == 14 then
            let p = (s & 0x3F0) | 15 in
            if transp p s != prob.inf then count + 1 else count
          else count
        in
        -- down
        let count =
          if s & 15 != 15 && s & 15 != 14 then
            let p = (s & 0x3F0) | ((s & 15) + 1) in
            if transp p s != prob.inf then count + 1 else count
          else count
        in
        count)
      (map state.i64 (iota nstates))
  in
  let npreds = reduce (\a b -> if a > b then a else b) 0 pred_count in
  map
    (\s ->
      let preds = replicate npreds (state.i64 (-1)) in
      let i = 0 in
      -- inter
      let (i, preds) = loop (i, preds) for a < 4 do
        let p = (a << 8) | (((s >> 6) & 0xF) << 4) | 0 in
        if transp p s != prob.inf then (i+1, preds with [i] = p)
        else (i, preds)
      in
      -- max
      let (i, preds) =
        if s & 15 == 15 then
          let p = s in
          if transp p s != prob.inf then (i+1, preds with [i] = p)
          else (i, preds)
        else (i, preds)
      in
      -- from_max
      let (i, preds) =
        if s & 15 == 14 then
          let p = (s & 0x3F0) | 15 in
          if transp p s != prob.inf then (i+1, preds with [i] = p)
          else (i, preds)
        else (i, preds)
      in
      -- down
      let (_, preds) =
        if (s & 15) != 15 && (s & 15) + 1 != 15 then
          let p = (s & 0x3F0) | ((s & 15) + 1) in
          if transp p s != prob.inf then (i+1, preds with [i] = p)
          else (i, preds)
        else (i, preds)
      in
      preds)
    (map state.i64 (iota nstates))

-- Main entry point to the program.
entry viterbi [n][m]
  (table_outputProb : [64][101]prob_t) (table_initialProb : [64][16]prob_t)
  (table_trans1 : [64][64]prob_t) (table_trans2 : [16]prob_t) (table_gamma : prob_t)
  (input_signals : [n][m]obs_t) (batch_size : i64) (batch_overlap : i64)
  : [n][]state_t =

  let transp (x : state_t) (y : state_t) =
    transition_probability table_trans1 table_trans2 table_gamma x y
  in
  let outp (x : state_t) (output : obs_t) =
    output_probability table_outputProb x output
  in
  let initp (x : state_t) =
    initial_probability table_initialProb x
  in
  let batch_output_size = batch_size - batch_overlap in
  let nbatches = (m - batch_overlap) / batch_output_size in
  let outsz = nbatches * batch_output_size in
  let preds = find_predecessors transp nstates in
  map
    (\signal ->
      let bacc = tabulate nbatches (\_ -> tabulate batch_output_size (\_ -> 0)) in
      let bacc = loop bacc for i < nbatches do
        let ofs = i * batch_output_size in
        let batch = signal[ofs:ofs+batch_size] in
        let out = main_viterbi preds transp initp outp batch in
        bacc with [i] = out[0:batch_output_size]
      in
      flatten bacc :> [outsz]state_t)
    input_signals
