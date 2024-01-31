import numpy as np
from trellis import HMM
import math

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
signal = [2, 2, 3, 2, 3, 2, 2, 2, 3, 3]
enc_signal = [x-2 for x in signal]
hmm = HMM(tables)

# The correct table from the origin is presented below; we expect our output
# to be equal to the sum of each column, depending on our choice of the length
# of the sequence.
#
# time       | 1    2    3      4       5       6       7       8       9       10
# obs        | 2    2    3      2       3       2       2       2       3       3
# alpha_t(1) | 0.0  0.0  0.0625 0.00000 0.00391 0.00000 0.00000 0.00000 0.00009 0.00007
# alpha_t(2) | 0.0  0.25 0.0000 0.01562 0.00000 0.00098 0.00049 0.00037 0.00000 0.00000
# alpha_t(3) | 1.0  0.5  0.0000 0.00000 0.00000 0.00000 0.00049 0.00049 0.00000 0.00000
# alpha_t(4) | 0.0  0.25 0.0000 0.01562 0.00000 0.00098 0.00049 0.00037 0.00000 0.00000
# alpha_t(5) | 0.0  0.0  0.0625 0.00000 0.00391 0.00000 0.00000 0.00000 0.00009 0.00007
# -----------|-------------------------------------------------------------------------
# sum        | 1.0  1.0  0.125  0.03124 0.00782 0.00196 0.00147 0.00123 0.00018 0.00014

expected = [1.0, 1.0, 0.125, 0.03124, 0.00782, 0.00196, 0.00147, 0.00123, 0.00018, 0.00014]
for n in range(1, len(signal)+1):
    p = hmm.forward([enc_signal[0:n]])
    err = abs(math.exp(p[0]) - expected[n-1])
    print(f"t={n} error: {err}")
