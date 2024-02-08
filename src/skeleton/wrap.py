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

def pick_non_pred(preds, n):
    if len(preds) == n:
        return None
    i = 0
    while i < len(preds):
        if preds[i] != i:
            return i
        i += 1
    return i

# Futhark requires the predecessors (a 2d array) to be regular, i.e., each
# inner array must have the same size. For both the Forward and the Viterbi
# algorithms, we pad with a state that is not actually a predecessor, as this
# does not impact the final result.
def pad_predecessors(src):
    nstates = len(src)
    maxpreds = max([len(p) for p in src])
    preds = np.zeros((nstates, maxpreds), dtype=int)
    for i, p in enumerate(preds):
        n = len(src[i])
        pad_value = pick_non_pred(src[i], n)
        p[:n] = src[i]
        p[n:] = [pad_value for j in range(n, maxpreds)]
    return preds

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
    def viterbi(self, signals):
        padded_signals = pad_signals(signals, self.boutsz, self.boverlap)
        res = self.hmm.viterbi(self.model, self.preds, padded_signals)
        output = self.hmm.from_futhark(res)
        return unpad_outputs(output, signals)

    def forward(self, signals):
        lens = np.array([len(x) for x in signals])
        padded_signals = pad_signals(signals, 0, 0)
        if self.gpuTarget:
            fut = self.hmm.forward_gpu(self.model, self.preds, padded_signals)
            out = self.hmm.log_sum_exp_entry(fut, lens)
        else:
            out = self.hmm.forward_cpu(self.model, self.preds, padded_signals, lens)
        return self.hmm.from_futhark(out)

