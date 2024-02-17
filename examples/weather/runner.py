import numpy as np
from trellis import HMM

signal = [0, 0, 0, 0, 0, 0, 0]
hmm = HMM({})
states = hmm.viterbi([signal])
for s in states[0]:
    if s == 0:
        print("Sunny", end=" ")
    else:
        print("Rainy", end=" ")
