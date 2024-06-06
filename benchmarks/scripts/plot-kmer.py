import matplotlib as mpl
mpl.use('Agg')

import matplotlib.pyplot as plt
import numpy as np
import json

from colors import colors

def load_full_time_label(label, conf, k):
    try:
        with open(f"out/{label}-{k}mer-{conf}.json", "r") as f:
            data = json.loads(f.read().strip())
            res = data["results"][0]
            return res["mean"], res["stddev"]
    except:
        return 0.0, 0.0

def load_alg_exec_time_label(label, conf, k):
    try:
        with open(f"out/{label}-{k}mer-{conf}.txt", "r") as f:
            data = [float(x.strip()) for x in f.readlines()]
            return np.average(data), np.std(data)
    except:
        return 0.0, 0.0

# Plot Forward algorithm results for kmer model
labels = [ "z", "pc", "pg", "tc", "tr" ]
x = np.arange(len(labels))

fig, axs = plt.subplots(layout="constrained")
axs.grid(which="both")
axs.set_axisbelow(True)
width = 0.45

avgs, errs = zip(*[load_full_time_label(label, "forward", 3) for label in labels])
bars = axs.bar(x, avgs, width, yerr=errs, label="F", color=colors[0])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label(label, "forward", 3) for label in labels])
bars = axs.bar(x + width, avgs, width, yerr=errs, label="A", color=colors[1])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

axs.set_xticks(x+0.5*width, [l.upper() for l in labels])
axs.set_yscale("log")
axs.set_ylabel("Execution time (s)")
axs.legend(loc="upper right", ncols=2)

fig.savefig("3mer-forward.pdf", bbox_inches="tight")

# Plot Viterbi algorithm results for kmer model (with and without batching)
labels = [ "s", "n", "tc", "tr" ]
x = np.arange(len(labels))

fig, axs = plt.subplots(layout="constrained")
axs.grid(which="both")
axs.set_axisbelow(True)

avgs, errs = zip(*[load_full_time_label(label, "nobatch-viterbi", 3) for label in labels])
bars = axs.bar(x, avgs, width, yerr=errs, label="F", color=colors[0])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label(label, "nobatch-viterbi", 3) for label in labels])
bars = axs.bar(x + width, avgs, width, yerr=errs, label="A", color=colors[1])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

axs.set_xticks(x + 0.5*width, [l.upper() for l in labels])
axs.set_yscale("log")
axs.set_ylabel("Execution time (s)")
axs.legend(loc="upper right", ncols=2)

fig.savefig("3mer-nobatch-viterbi.pdf", bbox_inches="tight")

# Plot Viterbi algorithm results for kmer models (with batching)
labels = [ "n", "tc", "tr" ]
x = np.arange(len(labels))
width = 0.15

fig, axs = plt.subplots(layout="constrained")
axs.grid(which="both")
axs.set_axisbelow(True)

avgs, errs = zip(*[load_full_time_label(label, "batch-viterbi", 3) for label in labels])
bars = axs.bar(x, avgs, width, yerr=errs, label="F (k = 3)", color=colors[0])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label(label, "batch-viterbi", 3) for label in labels])
bars = axs.bar(x + width, avgs, width, yerr=errs, label="A (k = 3)", color=colors[1])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_full_time_label(label, "batch-viterbi", 5) for label in labels])
bars = axs.bar(x + 2*width, avgs, width, yerr=errs, label="F (k = 5)", color=colors[2])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label(label, "batch-viterbi", 5) for label in labels])
bars = axs.bar(x + 3*width, avgs, width, yerr=errs, label="A (k = 5)", color=colors[3])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_full_time_label(label, "batch-viterbi", 7) for label in labels])
bars = axs.bar(x + 4*width, avgs, width, yerr=errs, label="F (k = 7)", color=colors[4])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_alg_exec_time_label(label, "batch-viterbi", 7) for label in labels])
bars = axs.bar(x + 5*width, avgs, width, yerr=errs, label="A (k = 7)", color=colors[5])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

axs.set_xticks(x + 2.5*width, [l.upper() for l in labels])
axs.set_yscale("log")
axs.set_ylabel("Execution time (s)")
axs.legend(loc="upper left")

fig.savefig("kmer-batch-viterbi.pdf", bbox_inches="tight")
