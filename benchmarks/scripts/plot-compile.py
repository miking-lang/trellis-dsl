import matplotlib as mpl
mpl.use('Agg')

import matplotlib.pyplot as plt
import numpy as np
import json

from colors import colors

def label_file(label, target):
    return f"out/{target}-{label}-compile.json"

def load_data(label, target):
    try:
        with open(label_file(label, target)) as f:
            data = json.loads(f.read().strip())
            res = data["results"][0]
    except:
        res = {"mean" : 0.0, "stddev" : 0.0}
    return res["mean"], res["stddev"]

labels = [ "weather", "3mer", "5mer", "7mer" ]
x = np.arange(len(labels))

fig, axs = plt.subplots(layout="constrained")
width = 0.4

avgs1, errs = zip(*[load_data(label, "tc") for label in labels])
bars = axs.bar(x, avgs1, width, yerr=errs, label="TC", color=colors[1])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

avgs2, errs = zip(*[load_data(label, "tr") for label in labels])
bars = axs.bar(x + width, avgs2, width, yerr=errs, label="TR", color=colors[2])
axs.bar_label(bars, fmt=lambda x: f"{x:.2f}" if x > 0 else "")

axs.set_xticks(x + 0.5*width, labels)
axs.set_ylabel("Compilation time (s)")
axs.legend(loc="upper left")

avgs = avgs1 + avgs2
ticks = np.arange(10, max(avgs), 10)
fmt = axs.yaxis.get_major_formatter()
labels = [fmt(x) for x in ticks]
axs.yaxis.set_ticks(ticks, labels=labels)
axs.grid(which="both")
axs.set_axisbelow(True)

fig.savefig("compilation.pdf", bbox_inches="tight")
