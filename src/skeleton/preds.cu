
__device__
uint32_t count_preds_warp(uint32_t src, uint32_t dst, int i) {
  // Update the count to 1 if the source state (src) of the current thread is a
  // predecessor of the target state (dst). Finally, we combine the results of
  // all threads using '__balloc_sync', which sets the bit of the threads with
  // non-zero count to 1, and the rest to 0.
  int count = 0;
  if (src < NUM_STATES && is_predecessor(src, dst, i)) {
    count = 1;
  }
  return __ballot_sync(0xFFFFFFFF, count);
}

extern "C"
__global__
void init_predecessors(uint32_t *pred_count) {
  uint32_t s = blockIdx.x * blockDim.x + threadIdx.x;
  int i = blockIdx.y;
  if (s < NUM_STATES) {
    pred_count[i * NUM_STATES + s] = 0;
  }
}

extern "C"
__global__
void count_predecessors(uint32_t *pred_count) {
  uint32_t dst = blockIdx.x;
  int i = blockIdx.y;
  if (dst < NUM_STATES) {
    for (uint32_t src = threadIdx.x; src < NUM_STATES; src += 32) {
      unsigned int c = count_preds_warp(src, dst, i);
      if (c != 0 && threadIdx.x == 0) {
        pred_count[i * NUM_STATES + dst] += __popc(c);
      }
    }
  }
}

__device__
void max_warp_reduce(volatile uint32_t *maxs, unsigned int tid) {
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
    const uint32_t* __restrict__ pred_count, uint32_t* __restrict__ result) {
  uint32_t idx = threadIdx.x;

  __shared__ uint32_t maxs[512];
  const uint32_t *pc = pred_count + blockIdx.x * NUM_STATES;
  maxs[idx] = pc[idx];
  for (uint32_t i = idx; i < NUM_STATES; i += 512) {
    if (pc[i] > maxs[idx]) {
      maxs[idx] = pc[i];
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
    result[blockIdx.x] = maxs[0];
  }
}

extern "C"
__global__
void compute_predecessors(
    uint32_t* __restrict__ preds, const uint32_t* __restrict__ max_preds) {
  uint32_t dst = blockIdx.x;
  int i = blockIdx.y;
  if (dst < NUM_STATES) {
    uint32_t *p = preds + i * NUM_STATES * max_preds[0] + dst * max_preds[0];
    uint32_t predc = 0;
    for (uint32_t src = threadIdx.x; src < NUM_STATES; src += 32) {
      uint32_t c = count_preds_warp(src, dst, i);
      if (c != 0 && threadIdx.x == 0) {
        do {
          uint32_t i = __ffs(c) - 1;
          p[predc++] = src + i;
          c = c & ~(1U << i);
        } while (c != 0);
      }
    }
    if (threadIdx.x == 0) {
      while (predc < max_preds[0]) {
        p[predc++] = NUM_STATES;
      }
    }
  }
}
