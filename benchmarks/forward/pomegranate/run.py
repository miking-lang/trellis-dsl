import pomegranate.hmm as hmm
from pomegranate.distributions import Categorical
import numpy as np
import torch

import common as c
import os
import sys
import time

def pad_signals(signals, lens):
    maxlen = max(lens)
    padded = np.zeros((len(signals), maxlen, 1), dtype=int)
    for i, s in enumerate(signals):
        for j in range(maxlen):
            if j < lens[i]:
                padded[i][j][0] = s[j]
            else:
                padded[i][j][0] = 0
    return padded

def forward(model, signals):
    lens = [len(x) for x in signals]
    padded_signals = pad_signals(signals, lens)
    out = model.forward(torch.from_numpy(padded_signals))
    return [torch.logsumexp(out[i, n-1, :], dim=0).item() for i, n in enumerate(lens)]

def build_model(model, initp, outp, transp):
    nstates = len(initp)
    dists = np.array([Categorical(np.array([outp[i]])) for i in range(nstates)])
    model.add_distributions(dists)
    for i in range(nstates):
        if initp[i] > 0.0:
            model.add_edge(model.start, dists[i], initp[i])
    for i in range(nstates):
        for j in range(nstates):
            if transp[i][j] > 0.0:
                model.add_edge(dists[i], dists[j], transp[i][j])
    return model

model_path = os.getenv("MODEL_PATH")
signals_path = os.getenv("SIGNALS_PATH")

if model_path:
    initp, outp, transp, signals = c.read_kmer_inputs(model_path, signals_path)
else:
    initp, outp, transp = c.get_weather_model()
    signals = c.read_weather_signals(signals_path)

use_gpu = int(sys.argv[1])
model = hmm.DenseHMM()
if use_gpu:
    model = model.cuda()
model = build_model(model, initp, outp, transp)

t0 = time.time()
p = forward(model, signals)
t1 = time.time()
print(t1-t0)
sys.stderr.write(str(p))
