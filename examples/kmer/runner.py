import sys
from math import log, inf
import time
import h5py
import numpy as np
from viterbi import viterbi

# Expands the transition probabilities from a 4 x 64 matrix to a 64 x 64
# matrix.
def expand_trans_probs(trans):
    exp_trans = np.zeros((64, 64), dtype=np.float32)
    for i in range(4):
        for j in range(4):
            for k in range(4):
                for l in range(4):
                    for m in range(4):
                        for n in range(4):
                            src_idx = 16 * i + 4 * j + k
                            dst_idx = 16 * l + 4 * m + n
                            exp_trans[src_idx][dst_idx] = trans[n][src_idx]
    return exp_trans

# Generates uniformly distributed initial positions among the states at layer
# zero. All other states have probability zero initially.
def generate_init_probs():
    init_probs = np.zeros((64, 16), dtype=np.float32)
    for kmer in range(0, 64):
        init_probs[kmer][0] = log(1.0 / 64.0)
        for layer in range(1, 16):
            init_probs[kmer][layer] = -inf
    return init_probs

def transform_output_probs(obs):
    output_probs = np.zeros((64, 101), dtype=np.float32)
    for i in range(64):
        idx = (i % 4) * 16 + ((i // 4) % 4) * 4 + (i // 16)
        for j in range(101):
            output_probs[i][j] = obs[j][idx]
    return output_probs

model_path = sys.argv[1]
signals_path = sys.argv[2]
with h5py.File(model_path, "r") as f:
    with np.errstate(divide="ignore"):
        obs = np.log(f['Tables']['ObservationProbabilities'][:])
    trans = np.log(f['Tables']['TransitionProbabilities'][:])
    duration = np.log(f['Tables']['DurationProbabilities'][:])
    tail_factor = np.log(f['Tables']['DurationProbabilities'].attrs['TailFactor'])
    trans1 = expand_trans_probs(trans)
    init_probs = generate_init_probs()
    output_probs = transform_output_probs(obs)
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
outputs = viterbi(signals, tables)

outc = ['A','C','G','T']
for i, signal in enumerate(outputs):
    print(f"Signal #{i+1}")
    for s in signal:
        if s % 16 == 0:
            print(outc[(s // 16) % 4], end="")
    print("")
