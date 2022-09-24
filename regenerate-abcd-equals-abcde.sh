ls benchmarks/abcd-equals-abcde \
  | sort -n \
  | grep '\.afa$' \
  | sed -r 's/\.afa$//; s/^[^-]+-//; s/-/ /g' \
  | Impact=true Bisim=true python3 abcd-equals-abcde.py -
