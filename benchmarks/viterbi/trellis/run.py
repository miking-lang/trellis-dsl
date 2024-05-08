import common as c
from trellis import HMM
import os
import sys
import time

model_path = os.getenv("MODEL_PATH")
signals_path = os.getenv("SIGNALS_PATH")

if model_path:
    tables, signals = c.read_kmer_inputs_trellis(model_path, signals_path)
else:
    tables, signals = c.get_weather_inputs_trellis(signals_path)

hmm = HMM(tables)

use_gpu = int(sys.argv[1])
if len(sys.argv) == 3:
    k = int(sys.argv[2])
else:
    k = 0

if k == 3 or k == 5:
    bsz = 100
elif k == 7:
    if use_gpu == 1:
        bsz = 3
    else:
        bsz = 15
else:
    bsz = 100

t0 = time.time()
output = hmm.viterbi(signals, 5)
t1 = time.time()
t2 = time.time()
p = hmm.forward(signals)
t3 = time.time()

outc = "ACGT"
for i, seq in enumerate(output):
    print(f"Seq #{i+1} ({p[i]})")
    col = 0
    for s in seq:
        if s // 16384 == 0:
            if col == 80:
                print("")
                col = 0
            col += 1
            print(f"{outc[s % 4]}", end="")
    print("")
print(t1-t0)
print(t3-t2)
