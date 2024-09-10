import numpy as np
import sys
import ctypes
import subprocess

if len(sys.argv) != 3:
    print("Invalid number of command-line arguments")
    exit(1)
nstates = int(sys.argv[1])
ncases = int(sys.argv[2])
if nstates < 2**8:
    state_type = np.dtype(np.uint8)
    state_ctype = ctypes.c_uint8
elif nstates < 2**16:
    state_type = np.dtype(np.uint16)
    state_ctype = ctypes.c_uint16
elif nstates < 2**32:
    state_type = np.dtype(np.uint32)
    state_ctype = ctypes.c_uint32
elif nstates < 2**64:
    state_type = np.dtype(np.uint64)
    state_ctype = ctypes.c_uint64
else:
    print(f"Predecessor runner supports up to 2^64 states")
    exit(1)

r = subprocess.run(["nvcc", "-O3", "--shared", "-Xcompiler", "-fPIC", "-o", "libpreds.so", "preds.cu"])
if r.returncode != 0:
    print("Compilation of CUDA code to compute the predecessors failed")
    print(r.stdout.decode())
    print(r.stderr.decode())

# Load shared library and configure the C functions
lib = ctypes.cdll.LoadLibrary("./libpreds.so")
clib = ctypes.cdll.LoadLibrary("libc.so.6")
lib.find_max_predecessors.argtypes = [
    ctypes.c_int,
]
lib.find_max_predecessors.restype = np.ctypeslib.ndpointer(dtype=state_type, ndim=1, flags="C_CONTIGUOUS")
lib.find_all_predecessors.argtypes = [
    ctypes.c_int,
    state_ctype,
]
lib.find_all_predecessors.restype = np.ctypeslib.ndpointer(dtype=state_type, ndim=1, flags="C_CONTIGUOUS")

ptr = lib.find_max_predecessors(ncases)
ctypes_ptr = ctypes.cast(ptr, ctypes.POINTER(state_ctype))
maxp = np.ctypeslib.as_array(ctypes_ptr, shape=(ncases,)).copy()
clib.free(ptr)

maxpreds = int(max(maxp))
ptr = lib.find_all_predecessors(ncases, maxpreds)
ctypes_ptr = ctypes.cast(ptr, ctypes.POINTER(state_ctype))
predecessors = np.ctypeslib.as_array(ctypes_ptr, shape=(ncases, nstates, maxpreds)).copy()
clib.free(ptr)

for i in range(ncases):
    p = predecessors[i].transpose()[:maxp[i]]
    np.save(f"pred{i}", p)
    print(maxp[i])
