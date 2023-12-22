import numpy as np
import h5py
import sys
from math import log, inf

# Expands the transition probabilities from a 4 x 64 matrix to a 64 x 64
# matrix.
def expand_trans_probs(trans):
    exp_trans = 64*[64*[0.0]]
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
    init_probs = 64*[16*[0.0]]
    for kmer in range(0, 64):
        init_probs[kmer][0] = log(1.0 / 64.0)
        for layer in range(1, 16):
            init_probs[kmer][layer] = -inf
    return init_probs

# Computes the predecessors of the model. This function is hard-coded for this
# particular model, where we know exactly how to compute the predecessors.
def generate_predecessors():
    preds = [[] for i in range(1024)]
    for x in range(0, 4):
        for y in range(0, 4):
            for z in range(0, 4):
                for layer in range(0, 16):
                    i = x * 256 + y * 64 + z * 16 + layer
                    # Predecessors from layer 0 shifting
                    for k in range(0, 4):
                        j = k * 256 + x * 64 + y * 16
                        preds[i].append(j)
                    if layer == 15:
                        preds[i].append(i)
                    else:
                        j = x * 256 + y * 64 + z * 16 + (layer + 1)
                        preds[i].append(j)
    return preds

# Pads all signals such that all signals have the same length and match the
# batch overlaps.
def pad_signals(signals):
    batch_size = 1024
    batch_overlap = 128
    lens = [len(s) for s in signals]
    maxlen = max(lens)
    batch_output_size = batch_size - batch_overlap
    lenpb = int(((maxlen + batch_output_size + 1) / batch_output_size) * batch_output_size + batch_overlap)
    for s in signals:
        for i in range(lenpb):
            if i < len(s):
                pass
            else:
                s.append(0)
    return signals

def produce_inputs(model_path, signals_path):
    with h5py.File(model_path, "r") as f:
        obs = np.log(f['Tables']['ObservationProbabilities'][:])
        trans = np.log(f['Tables']['TransitionProbabilities'][:])
        duration = np.log(f['Tables']['DurationProbabilities'][:])
        tail_factor = np.log(f['Tables']['DurationProbabilities'].attrs['TailFactor'])
        trans1 = expand_trans_probs(trans)
        init_probs = generate_init_probs()
        preds = generate_predecessors()
        print(f"outputProb: {len(obs)} {len(obs[0])}")
        print(f"initialProb: {len(init_probs)} {len(init_probs[0])}")
        print(f"trans1: {len(trans)} {len(trans[0])}")
        print(f"trans2: {len(duration)}")
        print(f"gamma: {tail_factor}")
        print(f"predecessors: {len(preds)} {len(preds[0])}")
    with h5py.File(signals_path, "r") as f:
        keys = list(f.keys())
        signals = [f[k]['Raw']['Signal'][:].tolist() for k in keys]
        padded_signals = pad_signals(signals)
        print(f"signals: {len(signals)}")
    with open("output-prob.txt", "w+") as f:
        f.write(f"{len(obs[0])} {len(obs)}\n")
        for i in range(len(obs[0])):
            for j in range(len(obs)):
                f.write(f"{obs[j][i]} ")
    with open("initial-prob.txt", "w+") as f:
        f.write(f"{len(init_probs)} {len(init_probs[0])}\n")
        for i in range(len(init_probs)):
            f.write(f"{' '.join([str(x) for x in init_probs[i]])}\n")
    with open("trans1.txt", "w+") as f:
        f.write(f"{len(trans1)} {len(trans1[0])}\n")
        for i in range(len(trans1)):
            f.write(f"{' '.join([str(x) for x in trans1[i]])}\n")
    with open("trans2.txt", "w+") as f:
        f.write(f"{len(duration)}\n")
        f.write(f"{' '.join([str(x) for x in duration])}\n")
    with open("gamma.txt", "w+") as f:
        f.write(f"{tail_factor}\n")
    with open("input-signals.txt", "w+") as f:
        f.write(f"{len(padded_signals)} {len(padded_signals[0])}\n")
        for s in padded_signals:
            f.write(f"{' '.join([str(x) for x in s])}\n")
    with open("predecessors.txt", "w+") as f:
        f.write(f"{len(preds)} {len(preds[0])}\n")
        for i in range(len(preds)):
            f.write(f"{' '.join([str(x) for x in preds[i]])}\n")

produce_inputs(sys.argv[1], sys.argv[2])
