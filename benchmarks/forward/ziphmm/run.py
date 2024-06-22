from pyZipHMM import *
import common as c
import os
import sys
import tempfile
import time
import numpy as np

model_path = os.getenv("MODEL_PATH")
signals_path = os.getenv("SIGNALS_PATH")

if len(sys.argv) != 2:
    print("Expected test identifier")
    exit(1)

test_id = sys.argv[1]
if test_id == "weather":
    initp, outp, transp = c.get_weather_model()
    signals = c.read_weather_signals(signals_path)
elif test_id.startswith("synthetic"):
    _, k = test_id.split("-")
    initp, outp, transp = c.get_synthetic_model(int(k))
    signals = c.read_synthetic_model_signals(signals_path)
elif test_id == "3mer" or test_id == "5mer" or test_id == "7mer":
    initp, outp, transp, signals = c.read_kmer_inputs(model_path, signals_path)
else:
    print(f"Unknown test identifier: {test_id}")
    exit(1)

init = Matrix(len(initp), 1)
out = Matrix(len(outp), len(outp[0]))
trans = Matrix(len(transp), len(transp[0]))
for i in range(len(initp)):
    init[i, 0] = initp[i]
for i in range(len(outp)):
    for j in range(len(outp[i])):
        out[i, j] = outp[i][j]
for i in range(len(transp)):
    for j in range(len(transp[i])):
        trans[i, j] = transp[i][j]

p = []
t = 0.0
for i, s in enumerate(signals):
    with tempfile.TemporaryDirectory() as tmpdir:
        with open(f"{tmpdir}/{i}.seq", "w+") as f:
            f.write(f"{' '.join([str(x) for x in s])}")

        fwd = Forwarder.fromSequenceDirectory(tmpdir, alphabetSize = len(outp[0]), nStatesSave = [len(outp)])
        t0 = time.time()
        p.append(fwd.ptforward(init, trans, out))
        t1 = time.time()
        t += t1-t0
print(t)

#np.savetxt("out.txt", p)

# Explicitly delete zipHMM objects here to avoid error on exit
del fwd
del init
del out
del trans
