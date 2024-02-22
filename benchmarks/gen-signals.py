import h5py
import numpy as np
import os
import random
import sys

nsignals = int(sys.argv[1])
signal_len = int(sys.argv[2])

# Use a seed to get a fixed result
random.seed(1234)

obs = [0, 1]
signals = [[x for x in random.choices(obs, k=signal_len)] for i in range(nsignals)]

# Write data using the HDF5 format
with h5py.File("signals/weather.hdf5", "w") as f:
    for i, s in enumerate(signals):
        sig_group = f.create_group(f"signal{i}")
        raw = sig_group.create_group("Raw")
        signal = raw.create_dataset("Signal", (len(s),), dtype='i')
        signal[:] = np.array(s)

# Using the format of StochHMM
def int_to_mood(i):
    if i == 0:
        return 'H'
    elif i == 1:
        return 'G'
with open("signals/weather.fasta", "w+") as f:
    for i, s in enumerate(signals):
        out = ''.join([int_to_mood(x) for x in s])
        f.write(f">signal{i}\n{out}\n")

# Read the HDF5 encoded signals and write them to the format of StochHMM
with h5py.File("signals/kmer.hdf5", "r") as f:
    keys = list(f.keys())
    signals = [f[k]['Raw']['Signal'][:].tolist() for k in keys]

with open("signals/kmer.fasta", "w+") as f:
    for i, s in enumerate(signals):
        out = ' '.join([str(x) for x in s])
        f.write(f">signal{i}\n{out}\n")
