import sys
import time

import common as c
from trellis import HMM

model_path = sys.argv[1]
signals_path = sys.argv[2]
tables, signals = c.read_kmer_inputs_trellis(model_path, signals_path)
hmm = HMM(tables)

t0 = time.time()
outputs = hmm.viterbi(signals, 100)
probs = hmm.forward(signals)
t1 = time.time()

outc = ['A','C','G','T']
for i, signal in enumerate(outputs):
    print(f"Signal #{i+1} ({probs[i]})")
    for s in signal:
        if s // 64 == 0:
            print(outc[s % 4], end="")
    print("")
print(t1-t0)
