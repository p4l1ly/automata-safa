[ -z $1 ] && { echo path argument expected >&2; exit 1 }

if [ -f $1 ]; then
  echo $1
else
  find $1 -name '*.mata'
fi | while read -r f; do
  mkdir -p pandized/$(dirname $f)
  cat $f | sed -r 's/^%Section t"[^"]*" /@/; s/^%Section /@/; /^@Regex$/{$!{N;s/^@Regex\n/@Regex\n%Main /}}; s/^@AFA Bits/@AFA-bits/; s/^@NFA CharRanges/@NFA-intervals\n%Alphabet chars/; s/@NFA Bits/@NFA-bits/; s/^%InitialStates/%Initial/; s/^%FinalStates/%Final/; s/^%InitialFormula/%Initial/; s/^%FinalFormula/%Final/;' > pandized/$f
done
