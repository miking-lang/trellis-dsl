import numpy as np
import _generated
from futhark_ffi import Futhark
import os

__location__ = os.path.realpath(
    os.path.join(os.getcwd(), os.path.dirname(__file__)))

def read_predecessors():
    preds_path = os.path.join(__location__, "predecessors.txt")
    if os.path.isfile(preds_path):
        with open(preds_path, "r") as f:
            preds = []
            for i, line in enumerate(f.readlines()):
                preds.append([int(x) for x in line.split(" ")])
    else:
        print("Could not find predecessor file")
        exit(1)
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

class HMM:
    # Futhark requires the predecessors (a 2d array) to be regular, i.e., each
    # inner array must have the same size. For both the Forward and the Viterbi
    # algorithms, we pad with a state that is not actually a predecessor, as this
    # does not impact the final result.
    def pad_predecessors(self, src):
        nstates = len(src)
        maxpreds = max([len(p) for p in src])
        preds = np.zeros((nstates, maxpreds), dtype=self.state_type)
        for i, p in enumerate(preds):
            n = len(src[i])
            pad_value = pick_non_pred(src[i], n)
            p[:n] = src[i]
            if pad_value:
                p[n:] = [pad_value for j in range(n, maxpreds)]
        return preds

    def pad_signals_viterbi(self, signals, lens):
        bos = self.batch_size - self.batch_overlap
        n = ((max(lens) + bos + 1) // bos) * bos + self.batch_overlap
        padded_signals = np.full((len(signals), n), -1, dtype=self.out_type)
        for i, s in enumerate(signals):
            padded_signals[i][:lens[i]] = s
        return padded_signals

    def viterbi(self, signals):
        lens = [len(s) for s in signals]
        padded_signals = self.pad_signals_viterbi(signals, lens)
        res = self.hmm.viterbi(self.model, self.preds, padded_signals)
        return [o[:lens[i]] for i, o in enumerate(self.hmm.from_futhark(res))]

    def pad_signals_forward(self, signals, n):
        padded_signals = np.zeros((len(signals), n), dtype=self.out_type)
        for i, s in enumerate(signals):
            padded_signals[i][:len(s)] = s
        return padded_signals

    def forward(self, signals):
        lens = np.array([len(x) for x in signals])
        padded_signals = self.pad_signals_viterbi(signals, lens)
        out = self.hmm.forward(self.model, self.preds, padded_signals)
        return self.hmm.from_futhark(out)

