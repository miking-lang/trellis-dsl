import numpy as np
import _generated
from futhark_ffi import Futhark
import os

__location__ = os.path.realpath(
    os.path.join(os.getcwd(), os.path.dirname(__file__)))

def read_predecessors():
    with open(os.path.join(__location__, "predecessors.txt"), "r") as f:
        preds = []
        for i, line in enumerate(f.readlines()):
            preds.append([int(x) for x in line.split(" ")])
    return preds

def pad_predecessors(src, f):
    nstates = len(src)
    maxpreds = max([len(p) for p in src])
    preds = np.zeros((nstates, maxpreds), dtype=int)
    for i, p in enumerate(preds):
        pad_value = f(src[i])
        for j in range(maxpreds):
            if j < len(src[i]):
                p[j] = src[i][j]
            else:
                p[j] = pad_value
    return preds

def pick_non_pred(preds, n):
    if len(preds) == n:
        return None
    i = 0
    while i < len(preds):
        if preds[i] != i:
            return i
        i += 1
    return i

# NOTE(larshum, 2024-01-31): Futhark requires arrays to be regular, i.e., if
# some states have more predecessors than others, we need to pad the 2d array
# to ensure all of them have the same inner size. As adding a branch in the GPU
# code results in a significant slowdown, we instead pad with a value we know
# won't impact the result:
# * For the Viterbi algorithm, repeating the last predecessor over and over
#   does not impact the final result, as we're only interested in the max
#   probability. However, this assumes all tasks have a predecessor.
# * For the Forward algorithm, we repeat a state which we know is not a
#   predecessor, as this won't impact our sum (the transition probability is
#   zero).
def pad_predecessors_viterbi(data):
    return pad_predecessors(data, lambda row: row[-1])

def pad_predecessors_forward(data):
    nstates = len(data)
    return pad_predecessors(data, lambda row: pick_non_pred(row, nstates))

def pad_signals(signals, bos, boverlap):
    lens = [len(s) for s in signals]
    if bos == 0:
        padded_len = max(lens)
    else:
        padded_len = ((max(lens) + bos + 1) // bos) * bos + boverlap
    padded_signals = np.zeros((len(signals), padded_len), dtype=np.float32)
    for i, s in enumerate(signals):
        padded_signals[i][0:len(s)] = s
    return padded_signals

def unpad_outputs(output, signals):
    lens = [len(s) for s in signals]
    out = []
    for i, o in enumerate(output):
        out.append(o[0:lens[i]])
    return out

class HMM:
    def __init__(self, args):
        preds = read_predecessors()
        self.vpreds = pad_predecessors_viterbi(preds)
        self.fwpreds = pad_predecessors_forward(preds)
        self.args = args
        self.hmm = Futhark(_generated)

