# Script for comparing the probabilities computed by the Forward algorithm for
# different tools. It computes the arithmetic mean and the standard deviation
# of the absolute difference in the probabilities reported by each pair of
# results.

import statistics
import sys


def read_output_file(o):
    with open(o, "r") as f:
        return [float(line) for line in f.readlines()]


def compare_probs(l1, l2):
    diffs = [abs(p1-p2) for p1, p2 in zip(l1, l2)]
    return sum(diffs), statistics.mean(diffs), statistics.stdev(diffs)


def run_comparison(probs, labels):
    for i in range(len(probs)):
        for j in range(i+1, len(probs)):
            print(f"Comparing {labels[i]} and {labels[j]}")
            assert len(probs[i]) == len(probs[j])
            sum, avg, stddev = compare_probs(probs[i], probs[j])
            print(f"{avg} ± {stddev} (total: {sum})")


def default_files(model):
    return [
        f"out/pc-sparse-{model}-forward-data.txt",
        f"out/pg-sparse-{model}-forward-data.txt",
        f"out/pc-dense-{model}-forward-data.txt",
        f"out/pg-dense-{model}-forward-data.txt",
        f"out/z-{model}-forward-data.txt",
        f"out/tc-{model}-forward-data.txt",
    ]

# The script automatically compares the benchmark outputs for both the weather
# and the 3mer model.
labels = [
    "Pomegranate Sparse CPU",
    "Pomegranate Sparse GPU",
    "Pomegranate Dense CPU",
    "Pomegranate Dense GPU",
    "ZipHMM",
    "Trellis"
]
weather_files = default_files("weather")
kmer_files = default_files("3mer")

# For the weather model, we find that all tools produce similar results.
# Trellis' result is close to pomegranate's sparse outputs, while the
# results of zipHMM differ the most from the others.
print("Weather model:")
weather_data = [read_output_file(o) for o in weather_files]
run_comparison(weather_data, labels)

# For the 3mer model, we find that all tools produce very similar results,
# because the provided observation sequences are much shorter.
print("="*20)
print("3mer model:")
kmer_data = [read_output_file(o) for o in kmer_files]
run_comparison(kmer_data, labels)
