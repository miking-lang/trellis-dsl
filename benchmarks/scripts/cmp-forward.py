# Script for performing a comparison of the probabilities computed by the
# Forward algorithm using different tools. The script print the probabilities
# for each case produced by each tool in a table.

import statistics
import sys


def read_output_file(o):
    with open(o, "r") as f:
        return [float(line) for line in f.readlines()]


def print_probs(probs, labels):
    padwidth = max([len(l) for l in labels])
    print("\t".join([""] + [f"{l:>{padwidth}}" for l in labels]))
    for i in range(len(probs[0])):
        print("\t".join([str(i)] + [f"{probs[j][i]:>{padwidth}}" for j in range(len(probs))]))


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


# Print the probabilities computed by the Forward algorithm for each case.
print("Weather model:")
weather_data = [read_output_file(o) for o in weather_files]
print_probs(weather_data, labels)

print()
print("3mer model:")
kmer_data = [read_output_file(o) for o in kmer_files]
print_probs(kmer_data, labels)
