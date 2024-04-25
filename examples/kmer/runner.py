import sys
from math import log, inf
import time
import h5py
import numpy as np
from trellis import HMM
import time

# Generates uniformly distributed initial positions among the states at layer
# zero. All other states have probability zero initially.
def generate_init_probs(k):
    init_probs = np.zeros((4**k, 16), dtype=np.float32)
    for kmer in range(0, 4**k):
        init_probs[kmer][0] = log(1.0 / float(4**k))
        for layer in range(1, 16):
            init_probs[kmer][layer] = -inf
    return init_probs

def reverse_index(i, k):
    return sum([(i // 4**x) % 4 * (4**(k-x-1)) for x in range(k)])

def transform_output_probs(obs, k):
    output_probs = np.zeros((4**k, 101), dtype=np.float32)
    for i in range(4**k):
        idx = reverse_index(i, k)
        for j in range(101):
            output_probs[i][j] = obs[j][idx]
    return output_probs

model_path = sys.argv[1]
signals_path = sys.argv[2]
with h5py.File(model_path, "r") as f:
    with np.errstate(divide="ignore"):
        obs = np.log(f['Tables']['ObservationProbabilities'][:])
    trans1 = np.log(f['Tables']['TransitionProbabilities'][:])
    duration = np.log(f['Tables']['DurationProbabilities'][:])
    tail_factor = np.log(f['Tables']['DurationProbabilities'].attrs['TailFactor'])
    kmer_length = f['Parameters'].attrs['KMerLength']
    init_probs = generate_init_probs(kmer_length)
    output_probs = transform_output_probs(obs, kmer_length)
with h5py.File(signals_path, "r") as f:
    keys = list(f.keys())
    signals = [f[k]['Raw']['Signal'][:].tolist() for k in keys]

tables = {
    'gamma': tail_factor,
    'trans1': trans1,
    'trans2': duration,
    'outputProb': output_probs,
    'initialProb': init_probs
}
hmm = HMM(tables)

t0 = time.time()
outputs = hmm.viterbi(signals)
probs = hmm.forward(signals)
t1 = time.time()

# Sketch of the interface to the Baum-Welch algorithm for training the HMM on
# given observation data. The result is the updated tables that we originally
# provided to the HMM. Should the model also update itself, as a side-effect,
# or should we create a new one ('hmm2 = HMM(upd_tables)')?
#for i in range(10):
#    A, B, pi = hmm.baum_welch(signals)
#    upd_tables = update_tables(A, B, pi)
#    hmm.update_tables(upd_tables)

outc = ['A','C','G','T']
for i, signal in enumerate(outputs):
    print(f"Signal #{i+1} ({probs[i]})")
    for s in signal:
        if s % 16 == 0:
            print(outc[(s // 16) % 4], end="")
    print("")
print(t1-t0)
