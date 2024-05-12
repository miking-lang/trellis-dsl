
__device__
bool is_predecessor(state_t src, state_t dst) {
  return transition_prob(src, dst, 0) == 0.0;
}

extern "C"
__global__
void init_predecessors(state_t *pred_count) {
  state_t s = blockIdx.x * blockDim.x + threadIdx.x;
  if (s < NUM_STATES) {
    pred_count[s] = 0;
  }
}

extern "C"
__global__
void count_predecessors(state_t *pred_count) {
  state_t dst = blockIdx.x * blockDim.x + threadIdx.x;
  if (dst < NUM_STATES) {
    for (state_t src = 0; src < NUM_STATES; src++) {
      if (is_predecessor(src, dst)) {
        atomicInc(pred_count + dst, NUM_STATES);
      }
    }
  }
}

__device__
void max_warp_reduce(volatile state_t *maxs, unsigned int tid) {
  if (maxs[tid + 32] > maxs[tid]) {
    maxs[tid] = maxs[tid + 32];
  }
  if (maxs[tid + 16] > maxs[tid]) {
    maxs[tid] = maxs[tid + 16];
  }
  if (maxs[tid + 8] > maxs[tid]) {
    maxs[tid] = maxs[tid + 8];
  }
  if (maxs[tid + 4] > maxs[tid]) {
    maxs[tid] = maxs[tid + 4];
  }
  if (maxs[tid + 2] > maxs[tid]) {
    maxs[tid] = maxs[tid + 2];
  }
  if (maxs[tid + 1] > maxs[tid]) {
    maxs[tid] = maxs[tid + 1];
  }
}

extern "C"
__global__
void max_pred_count(
    const state_t* __restrict__ pred_count, state_t* __restrict__ result) {
  state_t idx = threadIdx.x;

  __shared__ state_t maxs[512];
  maxs[idx] = pred_count[idx];
  for (state_t i = idx; i < NUM_STATES; i += 512) {
    if (pred_count[i] > maxs[idx]) {
      maxs[idx] = pred_count[i];
    }
  }
  __syncthreads();

  if (idx < 256) {
    if (maxs[idx + 256] > maxs[idx]) {
      maxs[idx] = maxs[idx + 256];
    }
  }
  __syncthreads();
  if (idx < 128) {
    if (maxs[idx + 128] > maxs[idx]) {
      maxs[idx] = maxs[idx + 128];
    }
  }
  __syncthreads();
  if (idx < 64) {
    if (maxs[idx + 64] > maxs[idx]) {
      maxs[idx] = maxs[idx + 64];
    }
  }
  __syncthreads();
  if (idx < 32) max_warp_reduce(maxs, idx);

  if (idx == 0) {
    result[0] = maxs[0];
  }
}

extern "C"
__global__
void compute_predecessors(state_t *preds) {
  state_t dst = blockIdx.x * blockDim.x + threadIdx.x;
  if (dst < NUM_STATES) {
    state_t predc = 0;
    for (state_t src = 0; src < NUM_STATES; ++src) {
      if (is_predecessor(src, dst)) preds[predc++] = src;
    }
  }
}