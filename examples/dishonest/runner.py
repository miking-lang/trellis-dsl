import numpy as np
from trellis import HMM
import math

hmm = HMM({})

# We encode the signal by subtracting one from each value, so that the lower
# bound becomes 0.
signal = [3,6,1,6]
enc_signal = [x-1 for x in signal]

for states in hmm.viterbi([enc_signal]):
    state_str = ['F', 'L']
    for s in states:
        print(state_str[s], end="")
    print("")
