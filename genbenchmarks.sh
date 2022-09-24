set -x

# rm -r benchmarks
# mkdir benchmarks
# 
# zsh regexes-to-nfa.sh > benchmarks/email-filter-nfa.mata
# 
# Impact=true Bisim=true python3 abcd-equals-abcde.py 100
# mv /tmp/abcd-equals-abcde benchmarks/
# 
# Impact=true Bisim=true python3 abcd-equals-abcde.py 100 --empty
# mv /tmp/abcd-equals-abcde benchmarks/abcd-equals-abcdd
# 
# rm -rf benchmarks/cox-unsat-inclusion
# zsh cox-unsat-inclusion.sh
# mv /tmp/cox-unsat-inclusion benchmarks/
# 
# rm -rf benchmarks/stranger
# zsh stranger.sh
# mv /tmp/stranger benchmarks/

export Smv=true
export Aiger=true
export Mona=true
export Afasat=true
# zsh convert-for-checkers.sh benchmarks/cox-unsat-inclusion
zsh convert-for-checkers.sh benchmarks/abcd-equals-abcdd
zsh convert-for-checkers.sh benchmarks/abcd-equals-abcde
zsh convert-for-checkers.sh benchmarks/stranger
