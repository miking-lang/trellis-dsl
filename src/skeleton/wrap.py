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

def pad_signals(signals, n):
    padded_signals = np.zeros((len(signals), n), dtype=int)
    for i, s in enumerate(signals):
        padded_signals[i][:len(s)] = s
    return padded_signals

def unpad_outputs(res, batch_indices, lens, batch_overlap):
    res_idx = [(i, list(r)) for i, r in zip(batch_indices, res)]
    outputs = len(lens) * [[]]
    for i, r in res_idx:
        # We skip the batch overlap for the first batch of each signal
        if len(outputs[i]) == 0:
            outputs[i] = r
        else:
            outputs[i] += r[batch_overlap:]
    for i, n in enumerate(lens):
        outputs[i] = outputs[i][:n]
    return outputs

def extract_batches(signal, batch_size, batch_overlap):
    batches = []
    ofs = 0
    while ofs < len(signal):
        batches.append(signal[ofs:ofs+batch_size])
        ofs += batch_size - batch_overlap
    return batches

class HMM:
    def viterbi(self, signals):
        lens = [len(s) for s in signals]
        if self.batch_size == 0:
            maxlen = max(lens)
            padded_signals = pad_signals(signals, maxlen)
            res = self.hmm.viterbi(self.model, self.preds, padded_signals)
            output = self.hmm.from_futhark(res)
            return [o[:lens[i]] for i, o in enumerate(output)]
        else:
            batches = [(i, b) for i, s in enumerate(signals) for b in extract_batches(s, self.batch_size, self.batch_overlap)]
            batch_indices, data = zip(*batches)
            pbatches = np.zeros((len(batches), self.batch_size), dtype=int)
            for i in range(len(batches)):
                pbatches[i][:len(data[i])] = data[i]
            res = self.hmm.viterbi(self.model, self.preds, pbatches)
            output = self.hmm.from_futhark(res)
            return unpad_outputs(output, batch_indices, lens, self.batch_overlap)

    def forward(self, signals):
        lens = np.array([len(x) for x in signals])
        padded_signals = pad_signals(signals, max(lens))
        if self.gpuTarget:
            fut = self.hmm.forward_gpu(self.model, self.preds, padded_signals)
            out = self.hmm.log_sum_exp_entry(fut, lens)
        else:
            out = self.hmm.forward_cpu(self.model, self.preds, padded_signals, lens)
        return self.hmm.from_futhark(out)

