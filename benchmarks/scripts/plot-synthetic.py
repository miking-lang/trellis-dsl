import matplotlib as mpl
mpl.use('Agg')

import matplotlib.pyplot as plt
import numpy as np
import json

from colors import colors
from names import display_name

def load_alg_exec_time_label(label, alg, k):
    try:
        with open(f"out/{label}-synthetic-{k}-{alg}.txt", "r") as f:
            # Skip output from the warmup round
            data = [float(x.strip()) for x in f.readlines()][1:]
            return np.average(data), np.std(data)
    except:
        return 0.0, 0.0

plt.rc("axes", labelsize=14)
plt.rc("axes", titlesize=16)
plt.rc("xtick", labelsize=14)
plt.rc("ytick", labelsize=14)
plt.rc("legend", fontsize=13)

# Plot synthetic results for Forward and Viterbi algorithms in one figure
labels = [ f"synthetic-{k}" for k in range(5) ]
x = np.arange(len(labels))

fig, axs = plt.subplots(layout="constrained")
width = 0.2

avgs, errs = zip(*[load_alg_exec_time_label("tc", "forward", k) for k in range(5)])
bars = axs.bar(x, avgs, width, yerr=errs, label="TC Forward", color=colors[0])
#axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label("tr", "forward", k) for k in range(5)])
bars = axs.bar(x + width, avgs, width, yerr=errs, label="TR Forward", color=colors[1])
#axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label("tc", "viterbi", k) for k in range(5)])
bars = axs.bar(x + 2*width, avgs, width, yerr=errs, label="TC Viterbi", color=colors[2])
#axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label("tr", "viterbi", k) for k in range(5)])
bars = axs.bar(x + 3*width, avgs, width, yerr=errs, label="TR Viterbi", color=colors[3])
#axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

axs.set_xticks(x+1.5*width, [display_name(l) for l in labels])
axs.set_ylabel("Execution time (s)")
axs.legend(loc="upper left", ncol=2)

fig.savefig("synthetic-results.pdf", bbox_inches="tight", pad_inches=0.05)
