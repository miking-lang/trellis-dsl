-- This file shows a sketch of how we could generate code from a model defined
-- using the Trellis DSL.

-- The parts marked as generated are to be determined by the number of states
-- available in the model, the number of possible observed values, and
-- potentially through configuration (e.g., whether to use 32- or 64-bit floats
-- or batching parameters). The native implementation should be sufficiently
-- generic that it can be copy-pasted into the generated parts of the code.

-----------------------------------
-- GENERATED INITIALIZATION CODE --
-----------------------------------

module state = u16
module obs = u8
module prob = f32

let nstates : i64 = 1024

-----------------------------------
-- NATIVE VITERBI IMPLEMENTATION --
-----------------------------------

type state_t = state.t
type obs_t = obs.t
type prob_t = prob.t

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
    let log_prob_from (s : state_t) (pre : state_t) : prob_t = chi[state.to_i64 pre] + transp pre s in
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
  let rest = signal[1:] in
  let chi1 = tabulate nstates (\s -> initp (state.i64 s) + outp (state.i64 s) x) in
  let r = viterbi_forward predecessors transp outp rest chi1 in
  match r
  case {chi = chi, zeta = zeta} ->
    let sLast = max_index_by_state chi in
    reverse (viterbi_backward (state.i64 sLast) (reverse zeta)) :> [m]state_t

let log_sum_exp (s : []prob_t) : prob_t =
  let x = prob.maximum s in
  if x == -prob.inf then x
  else x + prob.log (prob.sum (map (\y -> prob.exp(y - x)) s))

let main_forward [m] (predecessors : [nstates][]state_t) (transp : state_t -> state_t -> prob_t)
                     (outp : state_t -> obs_t -> prob_t) (initp : state_t -> prob_t)
                     (signal : [m]obs_t) : prob_t =
  let x = signal[0] in
  let alpha0 = tabulate nstates (\s -> initp (state.i64 s) + outp (state.i64 s) x) in
  let alphaTminus1 =
    loop alpha = alpha0 for t < m-1 do
      tabulate nstates (\i ->
        let sum = log_sum_exp (map (\j -> alpha[state.to_i64 j] + transp j (state.i64 i)) predecessors[i]) in
        let obs = outp (state.i64 i) (signal[t+1]) in
        sum + obs)
  in
  log_sum_exp alphaTminus1

--------------------
-- GENERATED CODE --
--------------------

-- Checks whether a pair of states belong to a particular set of transitions
let in_inter (x : state_t) (y : state_t) : bool =
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
  table_outputProb[state.to_i64 (x >> 4)][obs.to_i64 output]

let initial_probability (table_initialProb : [64][16]prob_t) (x : state_t) : prob_t =
  table_initialProb[state.to_i64 (x >> 4)][state.to_i64 (x & 15)]

let transition_probability
  (table_trans1 : [64][64]prob_t) (table_trans2 : [16]prob_t) (table_gamma : prob_t)
  (x : state_t) (y : state_t) : prob_t =

  if in_inter x y then
    table_trans1[state.to_i64 (x >> 4)][state.to_i64 (y >> 4)] + table_trans2[state.to_i64 (y & 15)]
  else if in_max x y then table_gamma
  else if in_from_max x y then prob.log (prob.exp 1.0 - prob.exp table_gamma)
  else if in_down x y then prob.log 1.0
  else prob.neg prob.inf

-- Viterbi entry point
entry viterbi [n][m]
  (table_gamma : prob_t)
  (table_trans1 : [64][64]prob_t)
  (table_trans2 : [16]prob_t)
  (table_outputProb : [64][101]prob_t)
  (table_initialProb : [64][16]prob_t)
  (table_predecessors : [nstates][]state_t)
  (input_signals : [n][m]obs_t)
  : [n][]state_t =

  let batch_size = 1024 in
  let batch_overlap = 128 in
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
  map
    (\signal ->
      -- We could run each batch in parallel here. By doing so, we do not
      -- reduce the memory usage, but we do improve performance further.
      let bacc = tabulate nbatches (\_ -> tabulate batch_output_size (\_ -> 0)) in
      let bacc = loop bacc for i < nbatches do
        let ofs = i * batch_output_size in
        let batch = signal[ofs:ofs+batch_size] in
        let out = main_viterbi table_predecessors transp initp outp batch in
        bacc with [i] = out[0:batch_output_size]
      in
      flatten bacc :> [outsz]state_t)
    input_signals

-- Forward algorithm entry point
entry forward [n][m]
  (gamma : prob_t)
  (trans1 : [64][64]prob_t)
  (trans2 : [16]prob_t)
  (outputProb : [64][101]prob_t)
  (initialProb : [64][16]prob_t)
  (predecessors : [nstates][]state_t)
  (input_signals : [n][m]obs_t)
  : [n]prob_t =

  let transp (x : state_t) (y : state_t) =
    transition_probability trans1 trans2 gamma x y
  in
  let outp (x : state_t) (o : obs_t) =
    output_probability outputProb x o
  in
  let initp (x : state_t) =
    initial_probability initialProb x
  in
  map (main_forward predecessors transp outp initp) input_signals
