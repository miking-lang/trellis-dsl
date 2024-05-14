import matplotlib as mpl
mpl.use('Agg')

import matplotlib.pyplot as plt
import numpy as np
import json

from colors import colors

def label_file(label, target, preds):
    return f"out/{target}-compile-{preds}-{label}.json"

def load_data(label, target, preds):
    with open(label_file(label, target, preds)) as f:
        data = json.loads(f.read().strip())
        res = data["results"][0]
        return res["mean"], res["stddev"]

labels = [ "weather", "3mer", "5mer", "7mer" ]
x = np.arange(len(labels))

fig, axs = plt.subplots(layout="constrained")
axs.grid(which="both", zorder=0)
width = 0.4

avgs, errs = zip(*[load_data(label, "tg", "preds") for label in labels])
bars = axs.bar(x, avgs, width, yerr=errs, label="TG", color=colors[1])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs, errs = zip(*[load_data(label, "tg", "nopreds") for label in labels])
bars = axs.bar(x + width, avgs, width, yerr=errs, label="TG-NP", color=colors[2])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

axs.set_xticks(x + width, labels)
axs.set_yscale("log")
axs.set_ylabel("Compilation time (s)")
axs.legend(loc="upper left", ncols=2)

avgs = avgs1 + avgs2 + avgs3
ticks = np.arange(10, max(avgs), 10)
fmt = axs.yaxis.get_major_formatter()
labels = [fmt(x) for x in ticks]
axs.yaxis.set_ticks(ticks, labels=labels)

fig.savefig("compilation.pdf", bbox_inches="tight")
