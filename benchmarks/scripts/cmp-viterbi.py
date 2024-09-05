# Script for comparing the output of the Viterbi algorithm from different
# tools. It computes a similarity score using the Smith-Waterman algorithm for
# each pair of the provided outputs - a positive score indicates the results
# are very similar.

from Levenshtein import distance
import math
import statistics
import sys

import common

def read_state_seq(arg):
    try:
        with open(arg) as f:
            return [str(line.strip()) for line in f.readlines()]
    except:
        # Produce an empty sequence, so that the comparison function knows to
        # skip this version and its corresponding label.
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


# Compares the state sequences produced running the weather model using
# different tools.
def compare_weather_state_diff(seqs, labels, weather_model, weather_obs):
    comp = [(label, seq) for label, seq in zip(labels, seqs) if len(seq) > 0]
    for i in range(len(comp)):
        l1, s1 = comp[i]
        p1 = compute_weather_state_seq_prob(s1, weather_model, weather_obs)
        for j in range(i+1, len(comp)):
            l2, s2 = comp[j]
            print(f"Comparing weather state probabilities of {l1} and {l2}")
            assert len(s1) == len(s2)
            p2 = compute_weather_state_seq_prob(s2, weather_model, weather_obs)
            diffs = [abs(a - b) for a, b in zip(p1, p2)]
            s, avg, stddev = sum(diffs), statistics.mean(diffs), statistics.stdev(diffs)
            print(f"{avg} ± {stddev} (total: {s})")

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
    weather_state_files = bench_output_files("weather")
    weather_model = common.get_weather_model()
    weather_obs = common.read_weather_signals("signals/weather.hdf5")
    kmer_files1 = bench_output_files("3mer-nobatch")
    kmer_files2 = bench_output_files("3mer-batch")

    # We compare the state sequences of the weather model by evaluating the
    # probability of the state sequence given the observed values. While the
    # edit distance between the sequences is rather long (as we would find by
    # computing the Levenshtein distance), the probabilities are rather close.
    # This shows that the rather small difference in probability (considering
    # each observation sequence consists of one million entries) can lead to
    # large differences in the most likely state sequence.
    print("Weather model:")
    weather_data = [read_state_seq(f) for f in weather_state_files]
    compare_weather_state_diff(weather_data, labels, weather_model, weather_obs)
    # Commented out because it is slow
    #run_comparison(weather_data, labels)

    # For the 3mer model results, we compare the sequence of nucleotides
    # encoded by the resulting state sequences. In this case, we find that the
    # edit distance between the results are quite small.
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
