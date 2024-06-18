import matplotlib as mpl
mpl.use('Agg')

import matplotlib.pyplot as plt
import numpy as np
import json

from colors import colors
from names import display_name

def load_full_time_label(label, alg):
    try:
        with open(f"out/{label}-weather-{alg}.json", "r") as f:
            data = json.loads(f.read().strip())
            res = data["results"][0]
            return res["mean"], res["stddev"]
    except:
        return 0.0, 0.0

def load_alg_exec_time_label(label, alg):
    try:
        with open(f"out/{label}-weather-{alg}.txt", "r") as f:
            # Skip output from the warmup round
            data = [float(x.strip()) for x in f.readlines()][1:]
            return np.average(data), np.std(data)
    except:
        return 0.0, 0.0

plt.rc("axes", labelsize=14)
plt.rc("axes", titlesize=16)
plt.rc("xtick", labelsize=14)
plt.rc("ytick", labelsize=14)
plt.rc("legend", fontsize=14)

# Plot Forward algorithm results
labels = [ "z", "pc", "pg", "tc" ]
x = np.arange(len(labels))

fig, axs = plt.subplots(layout="constrained")
width = 0.4

avgs, errs = zip(*[load_full_time_label(label, "forward") for label in labels])
bars = axs.bar(x, avgs, width, yerr=errs, label="Full", color=colors[0])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label(label, "forward") for label in labels])
bars = axs.bar(x + width, avgs, width, yerr=errs, label="Alg", color=colors[1])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

axs.set_xticks(x+0.5*width, [display_name(l) for l in labels])
axs.set_ylabel("Execution time (s)")
axs.legend(loc="upper left")

fig.savefig("weather-forward.pdf", bbox_inches="tight", pad_inches=0.05)

# Plot Viterbi algorithm results
labels = [ "s", "tc" ]
x = np.arange(len(labels))

fig, axs = plt.subplots(layout="constrained")

avgs, errs = zip(*[load_full_time_label(label, "viterbi") for label in labels])
bars = axs.bar(x, avgs, width, yerr=errs, label="Full", color=colors[0])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label(label, "viterbi") for label in labels])
bars = axs.bar(x + width, avgs, width, yerr=errs, label="Alg", color=colors[1])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

axs.set_xticks(x + 0.5*width, [display_name(l) for l in labels])
axs.set_ylabel("Execution time (s)")
axs.legend(loc="upper left")

fig.savefig("weather-viterbi.pdf", bbox_inches="tight", pad_inches=0.05)

