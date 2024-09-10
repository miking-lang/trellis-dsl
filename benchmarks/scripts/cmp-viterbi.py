# Script for comparing the output of the Viterbi algorithm from different
# tools. Note that this script takes a while to run (around one minute) due to
# the long observation sequences used in the weather model evaluation.
#
# We compute the actual probability of the resulting state sequence to
# evaluate the weather model results, by the definition of an HMM. The script
# then prints the probabilities produced by each case and for each tool in a
# table.
#
# For the 3mer model, the script compares the resulting nucleotide sequences
# (retrieved by interpreting the state sequences in a post-processing step of
# the runner scripts of the respective tool) by their edit distance using the
# Levenshtein algorithm.

import Levenshtein
import math
import statistics
import sys

import common

def read_state_seq(arg):
    try:
        with open(arg) as f:
            return [str(line.strip()) for line in f.readlines()]
    except:
        # Produce an empty state sequence to indicate that this case should be
        # skipped. We use this because not all tools support the weather model.
        return []


# Computes the probability of a given state sequence given the weather model
# and the sequence of observations.
def compute_weather_state_seq_prob(state_seqs, model, obs_seqs):
    def state_idx(s):
        if s == 'S':
            return 0
        elif s == 'R':
            return 1
        else:
            print(f"Invalid state {s}")
            exit(1)
    initp, outp, transp = model
    probs = []
    for obs, states in zip(obs_seqs, state_seqs):
        p = math.log(initp[obs[0]])
        prev_state = state_idx(states[0])
        for o, s in zip(obs[1:], states[1:]):
            s = state_idx(s)
            p += math.log(transp[prev_state][s]) + math.log(outp[s][o])
            prev_state = s
        probs.append(p)
    return probs


# Prints the computed probabilities of the state sequences produced by
# different tools running the weather model.
def print_weather_state_probs(seqs, labels, weather_model, weather_obs):
    comp = [(label, seq) for label, seq in zip(labels, seqs) if len(seq) > 0]
    probs = [compute_weather_state_seq_prob(s, weather_model, weather_obs) for _, s in comp]
    padwidth = max([len(l) for l, _ in comp])
    print("\t".join([""] + [f"{l:>{padwidth}}" for l, _ in comp]))
    for i in range(len(probs[0])):
        print("\t".join([str(i)] + [f"{probs[j][i]:>{padwidth}}" for j in range(len(comp))]))

def run_comparison(seqs, labels):
    comp = [(label, seq) for label, seq in zip(labels, seqs) if len(seq) > 0]
    for i in range(len(comp)):
        l1, s1 = comp[i]
        for j in range(i+1, len(comp)):
            l2, s2 = comp[j]
            print(f"Comparing {l1} and {l2}")
            assert len(s1) == len(s2)
            dists = [Levenshtein.distance(a, b) for a, b in zip(s1, s2)]
            print(sum(dists))


def bench_output_files(model):
    return [
        f"out/s-{model}-viterbi-data.txt",
        f"out/n-{model}-viterbi-data.txt",
        f"out/tc-{model}-viterbi-data.txt",
        f"out/tr-{model}-viterbi-data.txt",
    ]

# The script compares the (interpreted) results produced by running the Viterbi
# algorithm of different tools on the weather and 3mer model.
labels = [
    "StochHMM",
    "Native CUDA",
    "Trellis (compile-time)",
    "Trellis (runtime)",
]
weather_state_files = bench_output_files("weather")
weather_model = common.get_weather_model()
weather_obs = common.read_weather_signals("signals/weather.hdf5")
kmer_files1 = bench_output_files("3mer-nobatch")
kmer_files2 = bench_output_files("3mer-batch")

# We compare the state sequences of the weather model by evaluating the
# probability of the state sequence given the observed values.
print("Weather model:")
weather_data = [read_state_seq(f) for f in weather_state_files]
print_weather_state_probs(weather_data, labels, weather_model, weather_obs)

# For the 3mer model results, we compare the edit distance between the
# sequences of nucleotides encoded by the resulting state sequences.
print()
print("Kmer model (no batching):")
kmer_data = [read_state_seq(o) for o in kmer_files1]
run_comparison(kmer_data, labels)
print()
print("Kmer model (batching):")
kmer_data = [read_state_seq(o) for o in kmer_files2]
run_comparison(kmer_data, labels)
