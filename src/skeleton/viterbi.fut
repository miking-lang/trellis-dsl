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

let main_viterbi [m] (predecessors : [nstates][]state_t)
                     (initp : state_t -> prob_t) (outp : state_t -> obs_t -> prob_t)
                     (transp : state_t -> state_t -> prob_t)
                     (signal : [m]obs_t) : [m]state_t =
  let x = signal[0] in
  let rest = signal[1:m] in
  let chi1 = tabulate nstates (\s -> initp (state.i64 s) + outp (state.i64 s) x) in
  let r = viterbi_forward predecessors transp outp rest chi1 in
  match r
  case {chi = chi, zeta = zeta} ->
    let sLast = max_index_by_state chi in
    reverse (viterbi_backward (state.i64 sLast) (reverse zeta)) :> [m]state_t
