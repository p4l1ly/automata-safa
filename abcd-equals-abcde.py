import os
import subprocess
import random
from contextlib import suppress
import sys

visited = set()

subprocess.run(["rm", "-rf", "/tmp/abcd-equals-abcde/"])
os.mkdir("/tmp/abcd-equals-abcde")

wanted_count = sys.argv[1]
if wanted_count == '-':
    def ixs_gen():
        for line in sys.stdin:
            yield line.strip().split(" ")
else:
    wanted_count = int(wanted_count)
    empty_only = '--empty' in sys.argv
    def ixs_gen():
        count = 0
        while count < wanted_count:
            ixs = [random.randrange(75) for _ in range(4 if empty_only else 5)]
            if len(set(ixs)) != (4 if empty_only else 5):  # uniqueness of tuple elements
                continue
            if empty_only:
                last_ix = ixs[-1]
            ixs.sort()
            if empty_only:
                ixs.append(last_ix)
            ixs = tuple(ixs)
            if ixs in visited:  # uniqueness of tuples
                continue
            visited.add(ixs)
            yield [str(ix) for ix in ixs]
            count += 1


for i, ixs in enumerate(ixs_gen()):
    f = f"{i}-{'-'.join(ixs)}"
    print("AFA", i, ixs, f, file=sys.stderr, flush=True)
    subprocess.run(f"zsh abcd-equals-abcde.sh {' '.join(ixs)} > /tmp/abcd-equals-abcde/{f}.mata", shell=True)
    subprocess.run(f"mv /tmp/abcd-equals-abcde/abcd-abcde-neq.afa /tmp/abcd-equals-abcde/{f}.afa", shell=True)
    subprocess.run(f"mv /tmp/abcd-equals-abcde/abcd-equals-abcde.bisim /tmp/abcd-equals-abcde/{f}.bisim", shell=True)
    subprocess.run(f"mv /tmp/abcd-equals-abcde/abcd-equals-abcde.ada /tmp/abcd-equals-abcde/{f}.ada", shell=True)

subprocess.run("rm /tmp/abcd-equals-abcde/abcd.afa", shell=True)
subprocess.run("rm /tmp/abcd-equals-abcde/abcde.afa", shell=True)
subprocess.run("rm /tmp/abcd-equals-abcde/abcde-neg.afa", shell=True)
