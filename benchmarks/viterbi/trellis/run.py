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

output = []
t = 0.0
for i in range(0, len(signals), bsz):
    t0 = time.time()
    output += hmm.viterbi(signals[i:i+bsz])
    t1 = time.time()
    t += t1-t0
print(t)
