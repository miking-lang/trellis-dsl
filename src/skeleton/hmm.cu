
/////////////////////////////
// GENERAL IMPLEMENTATIONS //
/////////////////////////////

#ifdef PRECOMPUTE_PREDECESSORS
__device__
void forward_prob_predecessors(
    const prob_t *alpha_prev, int instance, state_t state, prob_t *probs,
    HMM_DECL_PARAMS) {
  state_t *predecessors = predecessor_table + state;
  for (state_t i = 0; i < NUM_PREDS; i++) {
    state_t pred = predecessors[i * NUM_STATES];
    probs[i] =
      alpha_prev[instance * NUM_STATES + pred] + transition_prob(pred, state, HMM_CALL_ARGS);
  }
}

__device__
void viterbi_max_predecessor(
    const prob_t *chi_prev, int instance, state_t state, state_t *maxs,
    prob_t *maxp, HMM_DECL_PARAMS) {
  state_t *predecessors = predecessor_table + state;
  for (state_t i = 0; i < NUM_PREDS; i++) {
    state_t pred = predecessors[i * NUM_STATES];
    prob_t p = chi_prev[instance * NUM_STATES + pred] + transition_prob(pred, state, HMM_CALL_ARGS);
    if (p > *maxp) {
      *maxs = pred;
      *maxp = p;
    }
  }
}
#endif

const prob_t inf = 1.0 / 0.0;

extern "C"
__global__
void forward_init(
    const obs_t* __restrict__ obs, int maxlen, prob_t* __restrict__ alpha_zero,
    HMM_DECL_PARAMS) {
  state_t state = blockIdx.x * blockDim.x + threadIdx.x;
  unsigned int instance = blockIdx.y;
  if (state < NUM_STATES) {
    obs_t x = obs[instance * maxlen];
    alpha_zero[instance * NUM_STATES + state] =
      init_prob(state, HMM_CALL_ARGS) + output_prob(state, x, HMM_CALL_ARGS);
  }
}

__device__
prob_t log_sum_exp(const prob_t* probs) {
  prob_t maxp = probs[0];
  for (int i = 1; i < NUM_PREDS; i++) {
    if (probs[i] > maxp) maxp = probs[i];
  }
  if (maxp == -inf) return maxp;
  prob_t sum = 0.0;
  for (int i = 0; i < NUM_PREDS; i++) {
    sum += expf(probs[i] - maxp);
  }
  return maxp + logf(sum);
}

extern "C"
__global__ void forward_step(
    const obs_t* __restrict__ obs, const int* __restrict__ obs_lens, int maxlen,
    const prob_t* __restrict__ alpha_prev, prob_t* __restrict__ alpha_curr,
#ifdef PRECOMPUTE_PREDECESSORS
    int t, prob_t* __restrict__ probs_table, HMM_DECL_PARAMS) {
#else
    int t, HMM_DECL_PARAMS) {
#endif
  state_t state = blockIdx.x * blockDim.x + threadIdx.x;
  unsigned int instance = blockIdx.y;
  if (state < NUM_STATES) {
    size_t idx = instance * NUM_STATES + state;
    if (t < obs_lens[instance]) {
      obs_t x = obs[instance * maxlen + t];
#ifdef PRECOMPUTE_PREDECESSORS
      prob_t *probs = probs_table + instance * NUM_STATES * NUM_PREDS + state * NUM_PREDS;
      forward_prob_predecessors(alpha_prev, instance, state, probs, HMM_CALL_ARGS);
#else
      prob_t probs[NUM_PREDS];
      int pidx = forward_prob_predecessors(alpha_prev, instance, state, probs, HMM_CALL_ARGS);
      while (pidx < NUM_PREDS) probs[pidx++] = -inf;
#endif
      alpha_curr[idx] = log_sum_exp(probs) + output_prob(state, x, HMM_CALL_ARGS);
    } else if (t == obs_lens[instance]) {
      // We only need to copy the alpha data once - past this point, both alpha
      // vectors will contain the same data.
      alpha_curr[idx] = alpha_prev[idx];
    }
  }
}

__device__
void forward_max_warp_reduce(volatile prob_t *maxp, unsigned int tid) {
  if (maxp[tid + 32] > maxp[tid]) {
    maxp[tid] = maxp[tid + 32];
  }
  if (maxp[tid + 16] > maxp[tid]) {
    maxp[tid] = maxp[tid + 16];
  }
  if (maxp[tid + 8] > maxp[tid]) {
    maxp[tid] = maxp[tid + 8];
  }
  if (maxp[tid + 4] > maxp[tid]) {
    maxp[tid] = maxp[tid + 4];
  }
  if (maxp[tid + 2] > maxp[tid]) {
    maxp[tid] = maxp[tid + 2];
  }
  if (maxp[tid + 1] > maxp[tid]) {
    maxp[tid] = maxp[tid + 1];
  }
}

extern "C"
__global__
void forward_max(
    const prob_t* __restrict__ alpha, prob_t* __restrict__ result) {
  unsigned int idx = threadIdx.x;
  unsigned int instance = blockIdx.x;
  unsigned int lo = instance * NUM_STATES;

  __shared__ prob_t maxp[512];
  if (idx < NUM_STATES) {
    maxp[idx] = alpha[lo + idx];
  } else {
    maxp[idx] = -inf;
  }
  for (int i = lo + idx + 512; i < lo + NUM_STATES; i += 512) {
    if (alpha[i] > maxp[idx]) {
      maxp[idx] = alpha[i];
    }
  }
  __syncthreads();
  
  if (idx < 256) {
    if (maxp[idx + 256] > maxp[idx]) {
      maxp[idx] = maxp[idx + 256];
    }
  }
  __syncthreads();
  if (idx < 128) {
    if (maxp[idx + 128] > maxp[idx]) {
      maxp[idx] = maxp[idx + 128];
    }
  }
  __syncthreads();
  if (idx < 64) {
    if (maxp[idx + 64] > maxp[idx]) {
      maxp[idx] = maxp[idx + 64];
    }
  }
  __syncthreads();
  if (idx < 32) forward_max_warp_reduce(maxp, idx);

  if (idx == 0) {
    result[instance] = maxp[0];
  }
}

__device__
void forward_sum_warp_reduce(volatile prob_t *psum, unsigned int tid) {
  psum[tid] = psum[tid] + psum[tid + 32];
  psum[tid] = psum[tid] + psum[tid + 16];
  psum[tid] = psum[tid] + psum[tid + 8];
  psum[tid] = psum[tid] + psum[tid + 4];
  psum[tid] = psum[tid] + psum[tid + 2];
  psum[tid] = psum[tid] + psum[tid + 1];
}

extern "C"
__global__
void forward_log_sum_exp(
    const prob_t* __restrict__ alpha, prob_t* __restrict__ result) {
  unsigned int idx = threadIdx.x;
  unsigned int instance = blockIdx.x;
  unsigned int lo = instance * NUM_STATES;

  // Retrieve the maximum value for the current instance, as computed in the
  // max kernel.
  prob_t maxp = result[instance];

  __shared__ prob_t psum[512];
  if (idx < NUM_STATES) {
    psum[idx] = expf(alpha[lo + idx] - maxp);
  } else {
    psum[idx] = 0.0;
  }
  for (int i = lo + idx + 512; i < lo + NUM_STATES; i += 512) {
    psum[idx] = psum[idx] + expf(alpha[i] - maxp);
  }
  __syncthreads();

  // Compute the sum of all these exponents
  if (idx < 256) psum[idx] = psum[idx] + psum[idx + 256];
  __syncthreads();
  if (idx < 128) psum[idx] = psum[idx] + psum[idx + 128];
  __syncthreads();
  if (idx < 64) psum[idx] = psum[idx] + psum[idx + 64];
  __syncthreads();
  if (idx < 32) forward_sum_warp_reduce(psum, idx);

  // The first thread of each block writes the result
  if (idx == 0) {
    result[instance] = maxp + logf(psum[0]);
  }
}

extern "C"
__global__
void viterbi_init(
    const obs_t* __restrict__ obs, int maxlen, prob_t* __restrict__ chi_zero,
    HMM_DECL_PARAMS) {
  state_t state = blockIdx.x * blockDim.x + threadIdx.x;
  unsigned int instance = blockIdx.y;
  if (state < NUM_STATES) {
    obs_t x = obs[instance * maxlen];
    chi_zero[instance * NUM_STATES + state] =
      init_prob(state, HMM_CALL_ARGS) + output_prob(state, x, HMM_CALL_ARGS);
  }
}

extern "C"
__global__
void viterbi_init_batch(
    const obs_t* __restrict__ obs, const int* __restrict__ obs_lens, int maxlen,
    const state_t* __restrict__ seq, prob_t* __restrict__ chi_zero, int t,
    HMM_DECL_PARAMS) {
  state_t state = blockIdx.x * blockDim.x + threadIdx.x;
  unsigned int instance = blockIdx.y;
  if (state < NUM_STATES) {
    if (t < obs_lens[instance]) {
      obs_t x = obs[instance * maxlen + t];
      state_t last_state = seq[instance * maxlen + t - 1];
      if (state == last_state) {
        chi_zero[instance * NUM_STATES + state] = output_prob(state, x, HMM_CALL_ARGS);
      } else {
        chi_zero[instance * NUM_STATES + state] = -inf;
      }
    }
  }
}

extern "C"
__global__
void viterbi_forward(
    const obs_t* __restrict__ obs, const int* __restrict__ obs_lens, int maxlen,
    prob_t* __restrict__ chi1, prob_t* __restrict__ chi2,
    state_t* __restrict__ zeta, int t, int k, HMM_DECL_PARAMS) {
  state_t state = blockIdx.x * blockDim.x + threadIdx.x;
  unsigned int instance = blockIdx.y;
  if (state < NUM_STATES) {
    prob_t *chi_prev, *chi_curr;
    if (k % 2 == 0) {
      chi_prev = chi2;
      chi_curr = chi1;
    } else {
      chi_prev = chi1;
      chi_curr = chi2;
    }
    size_t idx = instance * NUM_STATES + state;
    size_t zeta_idx = instance * BATCH_SIZE * NUM_STATES + (k-1) * NUM_STATES + state;
    if (t+k < obs_lens[instance]) {
      obs_t x = obs[instance * maxlen + t + k];
      state_t maxs;
      prob_t maxp = -inf;
      viterbi_max_predecessor(chi_prev, instance, state, &maxs, &maxp, HMM_CALL_ARGS);
      chi_curr[idx] = maxp + output_prob(state, x, HMM_CALL_ARGS);
      zeta[zeta_idx] = maxs;
    } else if (t+k == obs_lens[instance]) {
      // We only need to copy over chi data once - past this point, we know
      // both chi vectors will contain identical information. We continue
      // setting the zeta matrix as below to ensure we backtrack through it
      // correctly.
      chi_curr[idx] = chi_prev[idx];
      zeta[zeta_idx] = state;
    } else {
      zeta[zeta_idx] = state;
    }
  }
}

__device__
void viterbi_backward_warp_reduce(volatile prob_t *maxp, volatile state_t *maxs, unsigned int tid) {
  if (maxp[tid + 32] > maxp[tid]) {
    maxp[tid] = maxp[tid + 32];
    maxs[tid] = maxs[tid + 32];
  }
  if (maxp[tid + 16] > maxp[tid]) {
    maxp[tid] = maxp[tid + 16];
    maxs[tid] = maxs[tid + 16];
  }
  if (maxp[tid + 8] > maxp[tid]) {
    maxp[tid] = maxp[tid + 8];
    maxs[tid] = maxs[tid + 8];
  }
  if (maxp[tid + 4] > maxp[tid]) {
    maxp[tid] = maxp[tid + 4];
    maxs[tid] = maxs[tid + 4];
  }
  if (maxp[tid + 2] > maxp[tid]) {
    maxp[tid] = maxp[tid + 2];
    maxs[tid] = maxs[tid + 2];
  }
  if (maxp[tid + 1] > maxp[tid]) {
    maxp[tid] = maxp[tid + 1];
    maxs[tid] = maxs[tid + 1];
  }
}

extern "C"
__global__
void viterbi_backward(
    const prob_t* __restrict__ chi, const state_t* __restrict__ zeta,
    state_t* __restrict__ out, int maxlen, int T) {
  size_t idx = threadIdx.x;
  size_t instance = blockIdx.x;
  size_t lo = instance * NUM_STATES;

  __shared__ state_t maxs[512];
  __shared__ prob_t maxp[512];
  maxs[idx] = idx;
  if (idx < NUM_STATES) {
    maxp[idx] = chi[lo + idx];
  } else {
    maxp[idx] = -inf;
  }
  for (int i = lo + idx + 512; i < lo + NUM_STATES; i += 512) {
    if (chi[i] > maxp[idx]) {
      maxp[idx] = chi[i];
      maxs[idx] = i - lo;
    }
  }
  __syncthreads();

  if (idx < 256) {
    if (maxp[idx + 256] > maxp[idx]) {
      maxp[idx] = maxp[idx + 256];
      maxs[idx] = maxs[idx + 256];
    }
  }
  __syncthreads();
  if (idx < 128) {
    if (maxp[idx + 128] > maxp[idx]) {
      maxp[idx] = maxp[idx + 128];
      maxs[idx] = maxs[idx + 128];
    }
  }
  __syncthreads();
  if (idx < 64) {
    if (maxp[idx + 64] > maxp[idx]) {
      maxp[idx] = maxp[idx + 64];
      maxs[idx] = maxs[idx + 64];
    }
  }
  __syncthreads();
  if (idx < 32) viterbi_backward_warp_reduce(maxp, maxs, idx);

  // Run the backtracking sequentially from the maximum state using the first
  // thread for each instance.
  if (idx == 0) {
    state_t max_state = maxs[0];
    state_t *outptr = out + instance * maxlen + T;
    const state_t *zetaptr = zeta + instance * BATCH_SIZE * NUM_STATES;
    outptr[BATCH_SIZE-1] = max_state;
    for (int t = BATCH_SIZE-2; t >= 0; t--) {
      outptr[t] = zetaptr[t * NUM_STATES + outptr[t+1]];
    }
  }
}
