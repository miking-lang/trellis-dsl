# Script for comparing the output of the Viterbi algorithm from different
# tools. It computes a similarity score using the Smith-Waterman algorithm for
# each pair of the provided outputs - a positive score indicates the results
# are very similar.

import sys
from Levenshtein import distance


def read_state_seq(arg):
    try:
        with open(arg) as f:
            return [str(line.strip()) for line in f.readlines()]
    except:
        # Produce an empty sequence, so that the comparison function knows to
        # skip this version and its corresponding label.
        return []


def run_comparison(seqs, labels):
    comp = [(label, seq) for label, seq in zip(labels, seqs) if len(seq) > 0]
    for i in range(len(comp)):
        l1, s1 = comp[i]
        for j in range(i+1, len(comp)):
            l2, s2 = comp[j]
            print(f"Comparing {l1} and {l2}")
            assert len(s1) == len(s2)
            dists = [distance(a, b) for a, b in zip(s1, s2)]
            print(sum(dists))


def bench_output_files(model):
    return [
        f"out/s-{model}-viterbi-data.txt",
        f"out/n-{model}-viterbi-data.txt",
        f"out/tc-{model}-viterbi-data.txt",
        f"out/tr-{model}-viterbi-data.txt",
    ]

# If no arguments are provided, we compare the (interpreted) results produced
# by running the Viterbi algorithm of different tools on the weather and 3mer
# model.
if len(sys.argv) == 1:
    labels = [
        "StochHMM",
        "Native CUDA",
        "Trellis (compile-time)",
        "Trellis (runtime)",
    ]
    weather_files = bench_output_files("weather")
    kmer_files1 = bench_output_files("3mer-nobatch")
    kmer_files2 = bench_output_files("3mer-batch")

    print("Weather model:")
    weather_data = [read_state_seq(o) for o in weather_files]
    run_comparison(weather_data, labels)
    print("="*20)
    print("Kmer model (no batching):")
    kmer_data = [read_state_seq(o) for o in kmer_files1]
    run_comparison(kmer_data, labels)
    print("="*20)
    print("Kmer model (batching):")
    kmer_data = [read_state_seq(o) for o in kmer_files2]
    run_comparison(kmer_data, labels)
else:
    labels = sys.argv[1:]
    data = [read_state_seq(l) for l in labels]
    run_comparison(data, labels)
