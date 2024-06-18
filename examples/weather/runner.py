import numpy as np
from trellis import HMM

# The observation probabilities when the weather is sunny is 0.8 (Happy) and
# 0.2 (Grumpy), and when the weather is rainy, the corresponding probabilities
# are 0.4 and 0.6.
tables = {
    'outp' : np.log(np.array([[0.8, 0.2], [0.4, 0.6]]).flatten())
}
hmm = HMM(tables)

# We observe only Happy, in which case the most likely sequence of states
# should be only Sunny.
signal = [0, 0, 0, 0, 0, 0, 0]
states = hmm.viterbi([signal])
for s in states[0]:
    if s == 0:
        print("Sunny", end=" ")
    else:
        print("Rainy", end=" ")
