import numpy as np
import _generated
from futhark_ffi import Futhark
import os

__location__ = os.path.realpath(
    os.path.join(os.getcwd(), os.path.dirname(__file__)))

def read_predecessors():
    with open(os.path.join(__location__, "predecessors.txt"), "r") as f:
        [npreds, maxpreds] = [int(x) for x in f.readline().split(" ")]
        preds = np.zeros((npreds, maxpreds))
        for i in range(npreds):
            preds[i] = [int(x) for x in f.readline().split(" ")]
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

