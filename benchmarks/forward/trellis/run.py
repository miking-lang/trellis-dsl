import common as c
from trellis import HMM
import os
import sys
import time
import numpy as np

model_path = os.getenv("MODEL_PATH")
signals_path = os.getenv("SIGNALS_PATH")

if len(sys.argv) != 2:
    print("Expected test identifier as only argument")
    exit(1)

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

t0 = time.time()
p = hmm.forward(signals)
t1 = time.time()
print(t1-t0)

#np.savetxt("out.txt", p)
