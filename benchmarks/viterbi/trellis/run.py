import common as c
from trellis import HMM
import os
import sys
import time
import numpy as np

model_path = os.getenv("MODEL_PATH")
signals_path = os.getenv("SIGNALS_PATH")

test_id = sys.argv[1]
if test_id == "weather":
    tables, signals = c.get_weather_inputs_trellis(signals_path)
elif test_id.startswith("synthetic"):
    _, k = test_id.split("-")
    tables, signals = c.get_synthetic_model_trellis(signals_path, int(k))
elif test_id == "3mer" or test_id == "5mer" or test_id == "7mer":
    tables, signals = c.read_kmer_inputs_trellis(model_path, signals_path)
else:
    print(f"Unknown test identifier: {test_id}")
    exit(1)
hmm = HMM(tables)

if len(sys.argv) >= 3:
    k = int(sys.argv[2])
else:
    k = 0

if k == 7:
    bsz = 5
else:
    bsz = 100

output = hmm.viterbi(signals, bsz, True)

if len(sys.argv) == 4:
    with open(sys.argv[3], "w+") as f:
        if test_id == "weather" or test_id == "synthetic":
            for o in output:
                f.write(' '.join([str(x) for x in o]) + "\n")
        else:
            outc = "ACGT"
            for o in output:
                for x in o:
                    if x // 4**k == 0:
                        f.write(outc[x % 4])
                f.write("\n")
