import numpy as np
import time
from math import exp, log, inf
import sys
import h5py

def get_weather_model():
    initp = [0.5, 0.5]
    outp = [[0.8, 0.2], [0.5, 0.5]]
    transp = [[0.75, 0.25], [0.5, 0.5]]
    return initp, outp, transp

def read_weather_signals(signals_path):
    with h5py.File(signals_path, "r") as f:
        keys = list(f.keys())
        signals = [f[k]['Raw']['Signal'][:].tolist() for k in keys]
    return signals

def get_weather_inputs_trellis(signals_path):
    tables = {
        'sunnyObs' : np.log([0.8, 0.2])
    }
    return tables, read_weather_signals(signals_path)

# Generates uniformly distributed initial positions among the states at layer
# zero. All other states have probability zero initially.
def generate_init_probs(k):
    init_probs = np.zeros((16, 4**k), dtype=np.float32)
    for kmer in range(0, 4**k):
        init_probs[0][kmer] = log(1.0 / float(4**k))
    for layer in range(1, 16):
        for kmer in range(0, 4**k):
            init_probs[layer][kmer] = -inf
    return init_probs

def reverse_index(i, k):
    return sum([(i // 4**x) % 4 * (4**(k-x-1)) for x in range(k)])

def transform_output_probs(obs, k):
    output_probs = np.zeros((4**k, 101), dtype=np.float32)
    for i in range(4**k):
        idx = reverse_index(i, k)
        for j in range(101):
            output_probs[i][j] = obs[j][idx]
    return output_probs.transpose()

def read_kmer_inputs_trellis(model_path, signals_path):
    with h5py.File(model_path, "r") as f:
        with np.errstate(divide="ignore"):
            obs = np.log(f['Tables']['ObservationProbabilities'][:])
        trans1 = np.log(f['Tables']['TransitionProbabilities'][:])
        duration = np.log(f['Tables']['DurationProbabilities'][:])
        tail_factor = np.log(f['Tables']['DurationProbabilities'].attrs['TailFactor'])
        k = f['Parameters'].attrs['KMerLength']
        init_probs = generate_init_probs(k)
        trans1 = trans1.reshape(4, 4**k).transpose(1, 0).flatten()
        out_prob = transform_output_probs(obs, k).flatten()
    with h5py.File(signals_path, "r") as f:
        keys = list(f.keys())
        signals = [f[k]['Raw']['Signal'][:].tolist() for k in keys]
    tables = {
        'gamma': tail_factor,
        'trans1': trans1,
        'trans2': duration,
        'outputProb': out_prob,
        'initialProb': init_probs
    }
    return (tables, signals)

def read_kmer_inputs(model_path, signals_path):
    with h5py.File(model_path, "r") as f:
        obs = f['Tables']['ObservationProbabilities'][:]
        trans = f['Tables']['TransitionProbabilities'][:]
        duration = f['Tables']['DurationProbabilities'][:]
        gamma = f['Tables']['DurationProbabilities'].attrs['TailFactor']
        kmer_length = f['Parameters'].attrs['KMerLength']
    if signals_path:
        with h5py.File(signals_path, "r") as f:
            keys = list(f.keys())
            signals = [f[k]['Raw']['Signal'][:].tolist() for k in keys]
    else:
        signals = []

    nlayers = len(duration)
    nkmers = 4 ** kmer_length
    nstates = nlayers * nkmers

    initp = np.zeros((nstates), dtype=float)
    for kmer in range(nkmers):
        initp[kmer*16] = 1.0 / 64.0
        for layer in range(1, nlayers):
            initp[kmer*16+layer] = 0.0

    outp = np.zeros((nstates, 101), dtype=float)
    for kmer in range(nkmers):
        idx = reverse_index(kmer, kmer_length)
        for o in range(101):
            for layer in range(nlayers):
                outp[kmer*nlayers+layer][o] = obs[o][idx]

    transp = np.zeros((nstates, nstates), dtype=float)
    for src in range(nstates):
        for dst in range(nstates):
            if (src // 16) % (nkmers / 4) == (dst // 64) % (nkmers / 4) and src % 16 == 0:
                transp[src][dst] = trans[(src // 16) % 4][dst // 16] * duration[dst % 16]
            elif src // 16 == dst // 16:
                if src % 16 == 15 and dst % 16 == 15:
                    transp[src][dst] = gamma
                elif src % 16 == 15 and dst % 16 == 14:
                    transp[src][dst] = 1.0 - gamma
                elif dst % 16 == src % 16 - 1:
                    transp[src][dst] = 1.0
                else:
                    transp[src][dst] = 0.0
            else:
                transp[src][dst] = 0.0

    return initp, outp, transp, signals
