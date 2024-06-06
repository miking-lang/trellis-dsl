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

t0 = time.time()
p = hmm.forward(signals)
t1 = time.time()
print(t1-t0)
sys.stderr.write(str(p))
