from cuda import cuda, nvrtc
import numpy as np
import sys

def cuda_check(err):
    if isinstance(err, cuda.CUresult):
        if err != cuda.CUresult.CUDA_SUCCESS:
            raise RuntimeError(f"CUDA error: {cuda.cuGetErrorString(err)}")
    elif isinstance(err, nvrtc.nvrtcResult):
        if err != nvrtc.nvrtcResult.NVRTC_SUCCESS:
            raise RuntimeError(f"CUDA error: {nvrtc.nvrtcGetErrorString(err)}")
    else:
        raise RuntimeError(f"Unknown error type: {err}")

def compile_cuda(src):
    with open(src, "r") as f:
        cu = f.read()

    err, prog = nvrtc.nvrtcCreateProgram(str.encode(cu), bytes(src, 'utf-8'), 0, [], [])
    cuda_check(err)

    opts = [b"-default-device", b"-lineinfo"]
    err, = nvrtc.nvrtcCompileProgram(prog, len(opts), opts)
    cuda_check(err)

    err, ptxSize = nvrtc.nvrtcGetPTXSize(prog)
    cuda_check(err)
    ptx = b" " * ptxSize
    err, = nvrtc.nvrtcGetPTX(prog, ptx)
    cuda_check(err)

    err, = cuda.cuInit(0)
    cuda_check(err)
    err, cuDevice = cuda.cuDeviceGet(0)
    cuda_check(err)
    err, context = cuda.cuCtxCreate(0, cuDevice)
    cuda_check(err)
    ptx = np.char.array(ptx)
    err, module = cuda.cuModuleLoadData(ptx.ctypes.data)
    cuda_check(err)

    return context, module

def load_cuda_function(module, name):
    err, fun = cuda.cuModuleGetFunction(module, name)
    cuda_check(err)
    return fun

def copy_to_gpu(arg):
    sz = len(arg) * arg.itemsize
    err, gpu_data = cuda.cuMemAlloc(sz)
    cuda_check(err)
    err, = cuda.cuMemcpyHtoD(gpu_data, arg.ctypes.data, sz)
    cuda_check(err)
    return gpu_data

def copy_from_gpu(gpu_data, n, ty):
    result = np.zeros(n, dtype=ty)
    sz = n * result.itemsize
    err, = cuda.cuMemcpyDtoH(result.ctypes.data, gpu_data, sz)
    cuda_check(err)
    return result

if len(sys.argv) != 3:
    print("Invalid number of command-line arguments")
    exit(1)
nstates = int(sys.argv[1])
ncases = int(sys.argv[2])
state_type = np.dtype(np.uint32)

ctx, module = compile_cuda("preds.cu")
init_preds = load_cuda_function(module, b"init_predecessors")
count_preds = load_cuda_function(module, b"count_predecessors")
max_predc = load_cuda_function(module, b"max_pred_count")
compute_predecessors = load_cuda_function(module, b"compute_predecessors")

# 1. Fill 'pred_count' with the number of predecessors for each state and every
# case.
err, pred_count = cuda.cuMemAlloc(ncases * nstates * state_type.itemsize)
args = [np.array([int(pred_count)])]
args = np.array([arg.ctypes.data for arg in args], dtype=np.uint64)
tpb = 256
blocks = (nstates + tpb - 1) // tpb
err, = cuda.cuLaunchKernel(init_preds, blocks, ncases, 1, tpb, 1, 1, 0, 0, args.ctypes.data, 0)
cuda_check(err)
tpb = 32
err, = cuda.cuLaunchKernel(count_preds, nstates, ncases, 1, tpb, 1, 1, 0, 0, args.ctypes.data, 0)
cuda_check(err)

# 2. Compute the maximum number of predecessors by reducing the result from the
# previous kernel down to a single value. Finally, copy that value back to the
# CPU so we can compute how much memory to allocate for the final step. We do
# this for all cases in parallel.
err, maxpreds = cuda.cuMemAlloc(ncases * state_type.itemsize)
args = [np.array([int(pred_count)]), np.array([int(maxpreds)])]
args = np.array([arg.ctypes.data for arg in args], dtype=np.uint64)
cuda_check(err)
err, = cuda.cuLaunchKernel(max_predc, ncases, 1, 1, 512, 1, 1, 0, 0, args.ctypes.data, 0)
cuda_check(err)
maxp = np.zeros(ncases, dtype=state_type)
err, = cuda.cuMemcpyDtoH(maxp.ctypes.data, maxpreds, ncases * maxp.itemsize)
cuda_check(err)
err, = cuda.cuCtxSynchronize()
cuda_check(err)

# 3. Put the maximum number of predecessors of any case at the first index.
maxp_cpu = np.array(max(maxp), dtype=np.uint32)
err, = cuda.cuMemcpyHtoD(maxpreds, maxp_cpu.ctypes.data, maxp_cpu.itemsize)
cuda_check(err)

# 4. Compute the predecessors of each state for every case.
err, preds = cuda.cuMemAlloc(ncases * nstates * maxp_cpu * state_type.itemsize)
tpb = 32
args = [np.array([int(preds)]), np.array([int(maxpreds)])]
args = np.array([arg.ctypes.data for arg in args], dtype=np.uint64)
err, = cuda.cuLaunchKernel(compute_predecessors, nstates, ncases, 1, tpb, 1, 1, 0, 0, args.ctypes.data, 0)
cuda_check(err)
predecessors = np.zeros((ncases, nstates, maxp_cpu), dtype=state_type)
err, = cuda.cuMemcpyDtoH(predecessors, preds, ncases * nstates * maxp_cpu * predecessors.itemsize)
cuda_check(err)

# 5. For each case, write the predecessor result to a file and print the
# maximum number of predecessors for that case.
for i in range(ncases):
    p = predecessors[i].transpose()[:maxp[i]]
    np.save(f"pred{i}", p)
    print(maxp[i])
