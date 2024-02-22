import matplotlib as mpl
mpl.use('Agg')

import matplotlib.pyplot as plt
import numpy as np
import json

def label_file(label):
    return f"out/tg-viterbi-compile-{label}.json"

def load_data(label):
    with open(label_file(label)) as f:
        data = json.loads(f.read().strip())
        res = data["results"][0]
        return res["mean"], res["stddev"]

labels = [
    "weather",
    "3mer",
    "5mer",
    "7mer"
]

avgs, errs = zip(*[load_data(label) for label in labels])
fig, axs = plt.subplots(layout="constrained")
bars = axs.bar(labels, avgs, yerr = errs)
axs.bar_label(bars, fmt="%.2f")
axs.set_ylabel("Compilation time (s)")

fig.savefig("compilation.pdf", bbox_inches="tight")
