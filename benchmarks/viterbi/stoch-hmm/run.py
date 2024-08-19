import os
import subprocess
import sys

SIGNALS_PATH = os.environ["SIGNALS_PATH"]

test_id = sys.argv[1]
if test_id == "weather":
    pass
elif test_id == "3mer":
    pass
else:
    print(f"Unsupported test {test_id}")

# By default, we use the least verbose output format to minimize I/O overhead.
# However, when we want to store the output, we print an integer value
# corresponding to the state.
output_format = "-gff"
if len(sys.argv) == 3:
    output_format = "-path"

s = subprocess.run(["stochhmm", "-model", f"{test_id}.hmm", "-seq", signals_path, "-viterbi", output_format])

if len(sys.argv) == 3:
    with open(sys.argv[2], "w+") as f:
        f.write(s.stdout.decode())

exit(s.returncode)
