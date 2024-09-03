import os
import subprocess
import sys

signals_path = os.environ["SIGNALS_PATH"]

test_id = sys.argv[1]
if test_id == "weather" or test_id == "3mer":
    pass
else:
    print(f"Unsupported test {test_id}")

# By default, we use the least verbose output format to minimize I/O overhead.
# However, when we want to store the output, we print an integer value
# corresponding to the state.
output_format = "-gff"
if len(sys.argv) == 3:
    output_format = "-path"

s = subprocess.run(["stochhmm", "-model", f"{test_id}.hmm", "-seq", signals_path, "-viterbi", output_format], capture_output=True)

if len(sys.argv) == 3:
    with open(sys.argv[2], "w+") as f:
        if test_id == "weather":
            states = "SR" # The weather is either Sunny or Rainy
            result = [line for line in s.stdout.decode().split('\n') if len(line) > 0]
            seqs = []
            for i in range(0, len(result), 2):
                seq = ''.join([states[int(x)] for x in result[i+1].split(' ') if len(x) > 0])
                seqs.append(seq)
            f.write('\n'.join(seqs))
        else:
            nucleotides = "ACGT"
            result = [line for line in s.stdout.decode().split('\n') if len(line) > 0]
            nuc_seqs = []
            for i in range(0, len(result), 2):
                out = ""
                state_seq = [int(x) for x in result[i+1].split(' ') if len(x) > 0]
                for state in state_seq:
                    if state % 16 == 0:
                        out += nucleotides[(state // 64) % 4]
                nuc_seqs.append(out)
            f.write('\n'.join(nuc_seqs))

if s.returncode != 0:
    print(s.stderr.decode())

exit(s.returncode)
