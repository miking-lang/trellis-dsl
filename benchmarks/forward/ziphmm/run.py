from pyZipHMM import *
import common as c
import os
import sys
import tempfile
import time

model_path = os.getenv("MODEL_PATH")
signals_path = os.getenv("SIGNALS_PATH")

if model_path:
    initp, outp, transp, signals = c.read_kmer_inputs(model_path, signals_path)
else:
    initp, outp, transp = c.get_weather_model()
    signals = c.read_weather_signals(signals_path)

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

# Explicitly delete zipHMM objects here to avoid error on exit
del fwd
del init
del out
del trans
