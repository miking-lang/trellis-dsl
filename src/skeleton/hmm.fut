-----------------------------------
-- NATIVE VITERBI IMPLEMENTATION --
-----------------------------------

type forw_res [n][m] = {chi : [n]prob_t, zeta : [m][n]state_t}

let max_index_by_state (s : []prob_t) : i64 =
  let cmp = \a b -> if a.1 > b.1 then a else b in
  let is = map (\i -> (i, s[i])) (indices s) in
  (reduce cmp is[0] is[1:]).0

let max_pred (f : state_t -> prob_t) (s : []state_t) : (state_t, prob_t) =
  let max_cmp = \x y -> if x.1 > y.1 then x else y in
  let preds = map (\x -> (x, f x)) s in
  reduce max_cmp preds[0] preds[1:]

let viterbi_forward [m]
  (predecessors : [nstates][npreds]state_t)
  (transp : state_t -> state_t -> prob_t)
  (outp : state_t -> obs_t -> prob_t)
  (signal : [m]obs_t)
  (chi1 : [nstates]prob_t) : forw_res[nstates][m] =

  let zeta = tabulate m (\_ -> tabulate nstates (\_ -> state.i32 0)) in
  loop {chi, zeta} = {chi = chi1, zeta = zeta} for i < m do
    let x = signal[i] in
    let f = \dst src -> chi[state.to_i64 src] + transp src dst + outp dst x in
    let (new_zeta, new_chi) =
      unzip
        (tabulate nstates (\dst -> max_pred (f (state.i64 dst)) predecessors[dst]))
    in
    {chi = new_chi, zeta = zeta with [i] = new_zeta}

let viterbi_backward [m] (s_last : state_t) (zeta : [m][nstates]state_t) : [1+m]state_t =
  let acc = [s_last] ++ tabulate m (\_ -> state.i32 0) in
  loop acc for i < m do
    acc with [i+1] = zeta[i][state.to_i64 acc[i]]

let viterbi_helper [m]
  (predecessors : [nstates][npreds]state_t)
  (outp : state_t -> obs_t -> prob_t)
  (transp : state_t -> state_t -> prob_t)
  (chi0 : [nstates]prob_t)
  (signal : [m]obs_t) : [m]state_t =
  let r = viterbi_forward predecessors transp outp signal[1:m] chi0 in
  match r
  case {chi = chi, zeta = zeta} ->
    let sLast = max_index_by_state chi in
    reverse (viterbi_backward (state.i64 sLast) (reverse zeta)) :> [m]state_t

let viterbi_first_batch [m]
  (predecessors : [nstates][npreds]state_t)
  (initp : state_t -> prob_t)
  (outp : state_t -> obs_t -> prob_t)
  (transp : state_t -> state_t -> prob_t)
  (signal : [m]obs_t) : [m]state_t =
  let x = signal[0] in
  let chi0 = tabulate nstates (\s -> initp (state.i64 s) + outp (state.i64 s) x) in
  viterbi_helper predecessors outp transp chi0 signal

let viterbi_subseq_batch [m]
  (predecessors : [nstates][npreds]state_t)
  (outp : state_t -> obs_t -> prob_t)
  (transp : state_t -> state_t -> prob_t)
  (last_state : state_t)
  (signal : [m]obs_t) : [m]state_t =
  let chi0 =
    tabulate nstates (\s ->
      if state.i64 s == last_state then 0.0 else -prob.inf)
  in
  viterbi_helper predecessors outp transp chi0 signal

let log_sum_exp (s : []prob_t) : prob_t =
  let x = prob.maximum s in
  if x == -prob.inf then x
  else x + prob.log (prob.sum (map (\y -> prob.exp(y - x)) s))

let forward_helper_cpu
  (predecessors : [nstates][npreds]state_t)
  (initp : state_t -> prob_t)
  (outp : state_t -> obs_t -> prob_t)
  (transp : state_t -> state_t -> prob_t)
  (signal : []obs_t)
  (signal_len : i64) : prob_t =

  let x = signal[0] in
  let alpha0 = tabulate nstates (\s -> initp (state.i64 s) + outp (state.i64 s) x) in
  let alphaTminus1 = loop alpha = alpha0 for t < signal_len-1 do
    tabulate nstates (\i ->
      let sum =
        log_sum_exp
          (map
            (\pre -> alpha[state.to_i64 pre] + transp pre (state.i64 i))
            predecessors[i])
      in
      sum + outp (state.i64 i) signal[t+1])
  in
  log_sum_exp alphaTminus1

let forward_helper_gpu [m]
  (predecessors : [nstates][npreds]state_t)
  (initp : state_t -> prob_t)
  (outp : state_t -> obs_t -> prob_t)
  (transp : state_t -> state_t -> prob_t)
  (signal : [m]obs_t) : [m][nstates]prob_t =

  let x = signal[0] in
  let alpha = replicate m (replicate nstates prob.inf) in
  let alpha0 = tabulate nstates (\s -> initp (state.i64 s) + outp (state.i64 s) x) in
  let alpha = alpha with [0] = alpha0 in
  loop alpha = alpha for t < m-1 do
    let alphaPrev = alpha[t] in
    alpha with [t+1] =
      tabulate nstates (\i ->
        let sum =
          log_sum_exp
            (map
              (\pre -> alphaPrev[state.to_i64 pre] + transp pre (state.i64 i))
              predecessors[i])
        in
        sum + outp (state.i64 i) signal[t+1])

--------------------
-- GENERATED CODE --
--------------------
