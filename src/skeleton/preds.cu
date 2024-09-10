
#define gpuErrchk(ans) { gpuAssert((ans), __FILE__, __LINE__); }
inline void gpuAssert(cudaError_t code, const char *file, int line) {
  if (code != cudaSuccess) {
    fprintf(stderr, "[%s:%d] CUDA error: %s", file, line, cudaGetErrorString(code));
    exit(code);
  }
}

__device__
uint32_t count_preds_warp(state_t src, state_t dst, int i) {
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

__global__
void init_predecessors(state_t *pred_count) {
  state_t s = blockIdx.x * blockDim.x + threadIdx.x;
  int i = blockIdx.y;
  if (s < NUM_STATES) {
    pred_count[i * NUM_STATES + s] = 0;
  }
}

__global__
void count_predecessors(state_t *pred_count) {
  state_t dst = blockIdx.x;
  int i = blockIdx.y;
  if (dst < NUM_STATES) {
    for (size_t src = threadIdx.x; src < NUM_STATES; src += 32) {
      uint32_t c = count_preds_warp(src, dst, i);
      if (c != 0 && threadIdx.x == 0) {
        pred_count[i * NUM_STATES + dst] += __popc(c);
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

__global__
void max_pred_count(
    const state_t* __restrict__ pred_count, state_t* __restrict__ result) {
  state_t idx = threadIdx.x;

  __shared__ state_t maxs[512];
  const state_t *pc = pred_count + blockIdx.x * NUM_STATES;
  maxs[idx] = 0;
  for (size_t i = idx; i < NUM_STATES; i += 512) {
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

__global__
void compute_predecessors(
    state_t* __restrict__ preds, const state_t max_preds) {
  state_t dst = blockIdx.x;
  int i = blockIdx.y;
  if (dst < NUM_STATES) {
    state_t *p = preds + i * NUM_STATES * max_preds + dst * max_preds;
    state_t predc = 0;
    for (size_t src = threadIdx.x; src < NUM_STATES; src += 32) {
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
      while (predc < max_preds) {
        p[predc++] = NUM_STATES;
      }
    }
  }
}

extern "C"
state_t *find_max_predecessors(int ncases) {
  // Fill pred_count with the number of predecessors for each state and every
  // case.
  state_t *pred_count;
  gpuErrchk(cudaMalloc(&pred_count, ncases * NUM_STATES * sizeof(state_t)));
  int tpb = 256;
  int blocks = (NUM_STATES + tpb - 1) / tpb;
  dim3 blockdims(blocks, ncases, 1);
  dim3 threaddims(tpb, 1, 1);
  init_predecessors<<<blockdims, threaddims>>>(pred_count);
  gpuErrchk(cudaPeekAtLastError());

  blockdims = dim3(NUM_STATES, ncases, 1);
  threaddims = dim3(32, 1, 1);
  count_predecessors<<<blockdims, threaddims>>>(pred_count);
  gpuErrchk(cudaPeekAtLastError());

  // Compute the maximum number of predcessors by reducing the result from the
  // previous kernel to a single value. Finally, we copy that value back to the
  // CPU so we can compute the maximum among any case.
  state_t *maxpreds;
  gpuErrchk(cudaMalloc(&maxpreds, ncases * sizeof(state_t)));
  max_pred_count<<<ncases, 512>>>(pred_count, maxpreds);
  gpuErrchk(cudaPeekAtLastError());
  state_t *maxp = (state_t*)malloc(ncases * sizeof(state_t));
  gpuErrchk(cudaMemcpy(maxp, maxpreds, ncases * sizeof(state_t), cudaMemcpyDeviceToHost));

  // Free data and return the result.
  gpuErrchk(cudaFree(pred_count));
  gpuErrchk(cudaFree(maxpreds));
  return maxp;
}

extern "C"
state_t *find_all_predecessors(int ncases, state_t maxpreds) {
  // Compute the predecessors of each state and for every case.
  state_t *preds;
  gpuErrchk(cudaMalloc(&preds, ncases * NUM_STATES * maxpreds * sizeof(state_t)));
  dim3 blockdims(NUM_STATES, ncases, 1);
  dim3 threaddims(256, 1, 1);
  compute_predecessors<<<blockdims, threaddims>>>(preds, maxpreds);
  gpuErrchk(cudaPeekAtLastError());

  // Copy the result back to the CPU and return the result.
  state_t *result = (state_t*)malloc(ncases * NUM_STATES * maxpreds * sizeof(state_t));
  gpuErrchk(cudaMemcpy(result, preds, ncases * NUM_STATES * maxpreds * sizeof(state_t), cudaMemcpyDeviceToHost));
  gpuErrchk(cudaFree(preds));
  return result;
}
