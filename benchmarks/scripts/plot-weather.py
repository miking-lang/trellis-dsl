import matplotlib as mpl
mpl.use('Agg')

import matplotlib.pyplot as plt
import numpy as np
import json

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
            data = [float(x.strip()) for x in f.readlines()]
            return np.average(data), np.std(data)
    except:
        return 0.0, 0.0

# Plot Forward algorithm results
labels = [ "zc", "pc", "pg", "tc", "tg" ]
x = np.arange(len(labels))

fig, axs = plt.subplots(layout="constrained")
width = 0.4

avgs, errs = zip(*[load_full_time_label(label, "forward") for label in labels])
bars = axs.bar(x, avgs, width, yerr=errs, label="Full")
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label(label, "forward") for label in labels])
bars = axs.bar(x + width, avgs, width, yerr=errs, label="Forward")
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

axs.set_xticks(x+0.5*width, [l.upper() for l in labels])
axs.set_yscale("log")
axs.set_ylabel("Execution time (s)")
axs.legend(loc="upper right", ncols=2)

fig.savefig("weather-forward.pdf", bbox_inches="tight")

# Plot Viterbi algorithm results
labels = [ "sc", "tc", "tg" ]
x = np.arange(len(labels))

fig, axs = plt.subplots(layout="constrained")

avgs, errs = zip(*[load_full_time_label(label, "viterbi") for label in labels])
bars = axs.bar(x, avgs, width, yerr=errs, label="Full")
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label(label, "viterbi") for label in labels])
bars = axs.bar(x + width, avgs, width, yerr=errs, label="Viterbi")
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

axs.set_xticks(x + 0.5*width, [l.upper() for l in labels])
axs.set_yscale("log")
axs.set_ylabel("Execution time (s)")
axs.legend(loc="upper right", ncols=2)

fig.savefig("weather-viterbi.pdf", bbox_inches="tight")

