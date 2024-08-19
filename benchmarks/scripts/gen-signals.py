import h5py
import numpy as np
import os
import random
import sys

def write_hdf5_data(target, signals):
    with h5py.File(target, "w") as f:
        for i, s in enumerate(signals):
            sig_group = f.create_group(f"signal{i}")
            raw = sig_group.create_group("Raw")
            signal = raw.create_dataset("Signal", (len(s),), dtype='i')
            signal[:] = np.array(s)

def write_stochhmm_data(target, signals):
    with open(target, "w+") as f:
        for i, s in enumerate(signals):
            f.write(f">signal{i}\n{''.join(s)}\n")

if len(sys.argv) == 2:
    target = sys.argv[1]
elif len(sys.argv) != 4:
    print("Wrong number of command-line arguments")
    exit(1)
else:
    nsignals = int(sys.argv[1])
    signal_len = int(sys.argv[2])
    target = sys.argv[3]

    # Use a seed to get a fixed result
    random.seed(1234)

    obs = [0, 1]
    signals = [list(random.choices(obs, k=signal_len)) for i in range(nsignals)]

    # Write data using the HDF5 format
    write_hdf5_data(f"signals/{target}.hdf5", signals)

if target == "weather":
    mood = "HG"
    signals = [[mood[x] for x in s] for s in signals]
elif target == "synthetic":
    obs = "01"
    signals = [[obs[x] for x in s] for s in signals]
elif target == "kmer":
    # Read the HDF5 encoded signals and write them to the format of StochHMM
    with h5py.File("signals/kmer.hdf5", "r") as f:
        keys = list(f.keys())
        signals = [f[k]['Raw']['Signal'][:].tolist() for k in keys]

    with open("signals/kmer.fasta", "w+") as f:
        for i, s in enumerate(signals):
            out = ' '.join([str(x) for x in s])
            f.write(f">signal{i}\n{out}\n")
    exit(0)
else:
    print(f"Unknown target: {target}")
    exit(1)

# Write data using the format of StochHMM
write_stochhmm_data(f"signals/{target}.fasta", signals)
