# Simplifying Symbolic Alternating Finite Automata for Emptiness Testing

This repo contains symbolic alternating finite automaton preprocessing code
that we have presented at APLAS 2021 under the name "Simplifying Alternating
Finite Automata for Emptiness Testing" (authors: Pavol Vargovčík, Lukáš Holík).
The main executable is `ltle-to-afa`, which, despite its name, converts between
various representations of symbolic alternating finite automata (one of which
is LTL\_F), optionally performing simplification during the conversion. Its
main input and output formats are defined in the repo
[automata-safa-capnp](https://github.com/p4l1ly/automata-safa-capnp). It uses
the repo
[lens-recursion-schemes](https://github.com/p4l1ly/lens-recursion-schemes) for
as a library for many functions that are not specific for automata (mostly DAG
traversals and builders). There is a related project
[ltl-translators](https://github.com/p4l1ly/ltl-translators), which translates
between LTL standards and generates some LTL. Moreover, [my
fork](https://github.com/p4l1ly/symbolicautomata) of the model checker
[symbolicautomata](https://github.com/p4l1ly/symbolicautomata) contains a
program for conversion of Regex to NFA processable by this project. The fork
also adapts the symbolicautomata BISIM model checker. Other model checkers that
work with outputs of this project include:
[AFAMINISAT](https://github.com/p4l1ly/afaminisat),
[ABC](https://github.com/berkeley-abc/abc)
and [JAltImpact](https://github.com/p4l1ly/JAltImpact) (for me a more easily
installable fork of [JAltImpact](https://github.com/cathiec/JAltImpact)).

## How to build and run preprocessing and model checking

Consider the `./Dockerfile` as an installation manual for Ubuntu. But as for
the current state of the Dockerfile, it is buildable and runnable, but maybe
not so convenient for workflows where one wants to play around with the code.
In such case, install it to your machine accordingly, or improve the Dockerfile
--- we'll be happy to accept merge requests.

Build the docker image (this takes ~30 minutes and requires 4GB of free disk
space) which contains all the preprocessing executables as well as the model
checkers AfaMinisat, Bisim, ABC and JAltImpact. Together with the images for
our antichain (afaminisat), this is all the tooling that is necessary for the
experiment from our paper. For convenience, we have used higher level scripts,
like `reconvert` and `reconvert2`, but they are not adapted for the docker
image. Please consider them as more advanced examples of use in addition to
what we show here.

```
docker build -t automata-safa .
```

Run a container and enter its shell
```
docker run --name bench --network host -ti automata-safa bash
```

Convert some random LTL to AFA with various preprocessing approaches. Benchmark
indices, times, numbers of states, nodes and edges and preprocessing results
are logged to csv files. By preprocessing results we mean:
- 0: language emptiness has been proved without model checking
- 1: language emptiness has been disproved without model checking
- -1: model checking is needed
- other: an error occured

```
cd automata-safa-bench
tar xzf random-ltl.tgz
cd random-ltl/m15
mkdir bare basic up updown
# No preprocessing '(only structural hashing)'
cat ltls | head -n20 | ltle-to-afa -i ltl -o afaHashCons:bare | tee bare.csv
# Basic simplification
ltle-to-afa -i afa:bare -o afaBasicSimp:basic | tee basic.csv
# Up-shifting
ltle-to-afa -i afa:basic -o afaSimpGoblin:up | tee up.csv
# UpDown-shifting
ltle-to-afa -i afa:basic -o afaSimpGoblinMincut:updown | tee updown.csv
```

Now, let's convert the automata to various formats that are inputs for
corresponding model checkers. Let's go on only with the "up" preprocessing, the
other ones are analoguous (but the afaminisat model checker does not support 0
and 1 literals, so bare preprocessing might be a problem for it).
```
# FORMATTING
mkdir up-cnfafa up-sepDelaying up-smv up-smvReverse up-ada
# Antichain
ltle-to-afa -i afa:up -o cnfafa:up-cnfafa
# Bisimulation
ltle-to-afa -i afa:up -o sepafaDelaying:up-sepDelaying
# ABC '(smv)'
ltle-to-afa -i afa:up -o smv:up-smv
# ABC-reverse '(smv)'
ltle-to-afa -i afa:up -o smvReverseAssign:up-smvReverse
# JAltImpact
ltle-to-afa -i afa:up -o ada:up-ada

# To convert SMV to AIGER (the input for ABC), we'll use the standard tool.
mkdir up-aig up-aigReverse
# ABC '(aig)'
for f in $(ls up-smv); do ~/aiger/smvtoaig up-smv/$f > up-aig/$f; done
# ABC-reverse '(aig)'
for f in $(ls up-smvReverse); do ~/aiger/smvtoaig up-smvReverse/$f > up-aigReverse/$f; done
```

We can run the ABC tool right away. In the `reconvert` script, you can find
inspiration on how to format its output in the same way as the output of the
other model checkers (if there's a line "Output ... was asserted", the language
is nonempty, if there's a line "Property proved", then it is empty). 
```
BENCH=$PWD
cd ~/abc
# You may also try other ABC scripts, e.g.: drw; rf; b; drw; rwz; b; rfz; rwz; b;
./build/abc -c "read_aiger $BENCH/up-aig/19; b; rw; rf; b; rw; rwz; b; rfz; rwz; b; pdr -T 15"
./build/abc -c "read_aiger $BENCH/up-aigReverse/19; b; rw; rf; b; rw; rwz; b; rfz; rwz; b; pdr -T 15"
```

Similarly, we can run JAltImpact, which outputs EMPTY or NOT EMPTY:
```
cd ~/JAltImpact
cp $BENCH/up-ada/19 /tmp/jimpact.ada  # JAltImpact expects the .ada suffix
ant -Dmodel.path=/tmp/jimpact.ada
```

LTL benchmarks can be also generated randomly or systematically:
```
cd ~/automata-safa-bench
mkdir -p random-ltl/my-m15 parametric-ltl/counter
ltl-randgen-exe 6 16 0.8 0.9 0 0 0 0 1.00004 0 300 > random-ltl/my-m15/ltls
ltl-generator-exe counter 160 > parametric-ltl/counter/ltls
```

Generating RegexLib email filtering benchmarks:
```
cd ~/symbolicautomata/benchmarks
mkdir regexNfas
cat ~/automata-safa-bench/regexlib-email/regexes.txt | sh runtutor
mv regexNfas ~/automata-safa-bench/regexlib-email/nfa
cd ~/automata-safa-bench/regexlib-email/
mkdir filters
ltle-to-afa -i range16nfa:nfa -o afaHashCons:filters
mkdir -p abcd-abcdd/bare
cat choice.csv | head -n 150 | ltle-to-afa -i conjunctEq:0,1,2,3:0,1,2,3,3:filters -o afaHashCons:abcd-abcdd/bare | tee bare.csv
# We have the unpreprocessed benchmarks in abcd-abcdd/bare, continue in the same way as for the LTL example
```

Due to the lack of time and too dynamic nature of the development, I have not
implemented the standardized RPC interface for ABC and JAltImpact, so they had
to be invoked manually, each of them differently. Antichain and Bisimulation
have this interface. This is how you start the Bisimulation server:
```
# In a new shell (let's call this shell BISIM and the previous one BENCH)
docker run --name bisim -p 4001:4001 -ti automata-safa
cd symbolicautomata/benchmarks
sh solveafa  # this runs the server at port 4001
```

This is how you start the Antichain server (TODO Dockerfile):
```
# In a new shell (let's call this shell ANTICHAIN)
docker run --name antichain -p 4002:4002 -ti automata-safa
~/afaminisat/build/afaminisat 1 4002  # this runs the server at port 4002
```

Then, you have to start multisolvers, which are used for handling timeouts. The
concept of multisolvers is more complex but the implementation is incomplete.
They should be able to run multiple model checkers in parallel or in
pseudoparallel and if one of them finishes or a timeout occurs, all the model
checkings get stopped. For the sake of these benchmarks, they'll be used just
to handle timeouts and to make the interface more uniform for file solvers
(described later).
```
# In a new shell (let's call this shell BISIM-MULTI)
docker run --name bisim-multi --network host -ti automata-safa
~/automata-safa-capnp/build/multisolver 4041 15000 127.0.0.1:4001  # listen at 4041, bypass to 4001, timeout 15s
```

```
# In a new shell (let's call this shell ANTICHAIN-MULTI)
docker run --name antichain-multi --network host -ti automata-safa
~/automata-safa-capnp/build/multisolver 4042 15000 127.0.0.1:4002  # listen at 4042, bypass to 4002, timeout 15s
```

Finally, let's benchmark it all.
```
# In the BENCH shell
cd ~/automata-safa-bench/random-ltl/m15
# benchmark using Bisimulation
~/automata-safa-capnp/build/file-solver 127.0.0.1:4041 up-sepDelaying | tee up-sepDelaying-bisim.csv
# benchmark using Antichain
~/automata-safa-capnp/build/file-solver 127.0.0.1:4042 up-cnfafa | tee up-cnfafa-antichain.csv
```
