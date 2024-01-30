import numpy as np
from trellis import viterbi

tables = {
    'initp' : np.log(np.array([0.6, 0.4])),
    'outp' : np.log(np.array([[0.5, 0.4, 0.1], [0.1, 0.3, 0.6]])),
    'transp' : np.log(np.array([[0.7, 0.3], [0.4, 0.6]]))
}
# The observed sequence is ['normal', 'cold', 'dizzy']
# The most likely sequence of states is ['Healthy', 'Healthy', 'Fever']
signal = [0, 1, 2]
states = viterbi([signal], tables)
for s in states[0]:
    if s == 0:
        print("Healthy")
    else:
        print("Fever")
