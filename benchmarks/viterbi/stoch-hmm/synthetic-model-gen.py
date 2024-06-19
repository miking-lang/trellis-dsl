import common as c
import os
import sys

labels = ['0', '1']

def state_id(x):
    return f"STATE_{x}"

def trans_states(transp, x):
    nstates = len(transp)
    return "\n".join([f"  {state_id(y)}: {transp[x][y]}" for y in range(nstates) if transp[x][y] > 0])

def emission_states(outp, x):
    nobs = len(outp[0])
    return f"""@{" ".join([str(o) for o in range(nobs)])}
{" ".join([str(outp[x][o]) for o in range(nobs)])}
"""

def path_label(x):
    return f"  PATH_LABEL: {x}\n"

def print_state(outp, transp, x):
    return f"""
STATE:
  NAME: {state_id(x)}
{path_label(x)}TRANSITION: STANDARD: P(X)
{trans_states(transp, x)}
  END: 1
EMISSION: OBS: P(X)
  ORDER: 0
{emission_states(outp, x)}
"""

def init_state(initp):
    return f"""
STATE:
  NAME: INIT
TRANSITION: STANDARD: P(X)
{newline.join(["  " + state_id(x) + ": "+ str(initp[x]) for x in range(nstates) if initp[x] > 0])}
"""

if len(sys.argv) != 3:
    k = int(sys.argv[1])
    initp, outp, transp = c.get_synthetic_model(k)
    dst = sys.argv[2]
else:
    print("Expected k (all x±k are predecessors) as first argument and output path as second path")
    exit(1)

obs_vals = ','.join([str(x) for x in range(len(outp[0]))])
state_sep = "#############################################"
nstates = len(initp)
states_str = state_sep.join([print_state(outp, transp, x) for x in range(nstates)])
newline = "\n"
model_data = f"""
MODEL INFORMATION
======================================================
MODEL_NAME: SYNTHETIC MODEL

TRACK SYMBOL DEFINITIONS
======================================================
OBS: 0, 1

STATE DEFINITIONS
{state_sep}{init_state(initp)}{state_sep}{states_str}{state_sep}"""

with open(dst, "w+") as f:
    f.write(model_data)
