# Hallway problem from https://www.cs.mcgill.ca/~dprecup/courses/ML/Lectures/ml-lecture-hmm.pdf

import numpy as np
from trellis import HMM

# We always observe exactly two or exactly three walls
outp = [ [0.0, 1.0], [1.0, 0.0], [1.0, 0.0], [1.0, 0.0], [0.0, 1.0] ]

transp = [
    [0.75, 0.25, 0.0, 0.0, 0.0],
    [0.25, 0.5, 0.25, 0.0, 0.0],
    [0.0, 0.25, 0.5, 0.25, 0.0],
    [0.0, 0.0, 0.25, 0.5, 0.25],
    [0.0, 0.0, 0.0, 0.25, 0.75]
]

tables = {
    'outp' : np.log(np.array(outp)),
    'transp' : np.log(np.array(transp))
}
# Observations represent the number of walls we see at a particular state of
# a corridor, and it is deterministic.
# The observed sequence is [2, 2, 3, 2, 3, 2, 2, 2, 3, 3]
signal = [2, 2, 3, 2, 3, 2, 2, 2, 3, 3]
enc_signal = [x-2 for x in signal]
hmm = HMM(tables)
for n in range(1, len(signal)+1):
    p = hmm.forward([enc_signal[0:n]])
    print(f"{enc_signal[0:n]}: {p[0]}")
