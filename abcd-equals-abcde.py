import os
import subprocess
import random
import sys
import shutil

if len(sys.argv) != 3:
    print("fuck")
    exit()

visited = set()

REGEX_AUT_DIR = "regexNfas/"

dir_to_create_in = sys.argv[2]

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
    name_of_bench = '-'.join(ixs)
    print(f"{i}: {name_of_bench}")
    os.mkdir(name_of_bench)
    dir_of_bench = dir_to_create_in + "/" + name_of_bench
    emp_file_name = dir_of_bench + "/result_orig.emp"
    gen_aut_dir = dir_of_bench + "/gen_aut/"
    os.mkdir(gen_aut_dir)
    ixs = [f"aut{ix}" for ix in ixs]
    for ix in ixs:
        for ext in [".range16nfa", ".mata", "_mona.mata", ".afa"]:
            shutil.copyfile(REGEX_AUT_DIR + ix + ext, gen_aut_dir + ix + ext)
    with open(emp_file_name, 'w') as emp_file:
        for ix in ixs:
            print(f"load_automaton {ix}", file = emp_file)
        
        print(f"aut75 = (inter {' '.join(ixs[:-1])})", file = emp_file)
        # print(f"aut76 = (inter {ixs[-1]} aut75)", file = emp_file)
        # print(f"incl aut76 aut75", file = emp_file)
        print(f"incl aut75 {ixs[-1]}", file = emp_file)
