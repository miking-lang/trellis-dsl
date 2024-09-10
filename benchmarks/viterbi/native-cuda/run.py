import os
import re
import subprocess
import sys

model_path = os.environ["MODEL_PATH"]
signals_path = os.environ["SIGNALS_PATH"]

k = int(sys.argv[1])
batchsz = int(sys.argv[2])
if k == 3:
    p = 64
elif k == 5:
    p = 64
elif k == 7:
    p = 15
else:
    print(f"Unsupported value of k = {k}")
    exit(1)

# If we want to record output, we run the inputs sequentially as the order is
# not preserved by the tool when running in parallel.
if len(sys.argv) == 4:
    p = 1

s = subprocess.run(["./viterbicall", "-p", f"{p}", signals_path, "-m", model_path, f"--batch-size={batchsz}", "--batch-overlap=0", "--pure"], capture_output=True)
if s.returncode == 0:
    m = re.search(r"Decoding execution time : (\d+.\d+) s", s.stderr.decode())
    print(m.group(1))
else:
    print(f"Viterbicall failed: {s.stderr.decode()}")

if len(sys.argv) == 4:
    nucleotide = "ACGT"
    with open(sys.argv[3], "w+") as f:
        result = s.stdout.decode().split('\n')
        seqs = []
        acc = ""
        for line in result:
            if len(line) > 0 and line[0] == '>':
                if len(acc) > 0:
                    seqs.append(acc)
                    acc = ""
                continue
            acc += line
        if len(acc) > 0:
            seqs.append(acc)
        f.write('\n'.join(seqs))

exit(s.returncode)
