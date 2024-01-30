import numpy as np
import _generated
from futhark_ffi import Futhark
import os

__location__ = os.path.realpath(
    os.path.join(os.getcwd(), os.path.dirname(__file__)))

def read_predecessors():
    with open(os.path.join(__location__, "predecessors.txt"), "r") as f:
        data = []
        for i, line in enumerate(f.readlines()):
            data.append([int(x) for x in line.split(" ")])
    npreds = len(data)
    maxpreds = max([len(p) for p in data])
    preds = np.zeros((npreds, maxpreds))

    # We replicate the last predecessor over and over for states that have
    # fewer than the maximum number of predecessors. This avoids having to use
    # a special value to indicate non-existence (such as -1), which leads to a
    # significant performance degradation for Viterbi.
    for i, p in enumerate(preds):
        for j in range(maxpreds):
            last = data[i][-1]
            if j < len(data[i]):
                p[j] = data[i][j]
            else:
                p[j] = last
    return preds

def pad_signals(signals, lens, bos, boverlap):
    padded_len = ((max(lens) + bos + 1) // bos) * bos + boverlap
    padded_signals = np.zeros((len(signals), padded_len), dtype=np.float32)
    for i, s in enumerate(signals):
        padded_signals[i][0:len(s)] = s
    return padded_signals

def unpad_outputs(output, lens):
    out = []
    for i, o in enumerate(output):
        out.append(o[0:lens[i]])
    return out

