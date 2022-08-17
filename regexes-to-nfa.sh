set -e
rm -rf /tmp/email-filter-nfa
mkdir /tmp/email-filter-nfa

REGEX_PATH=../dantoni-symbolic/benchmarks/src/main/java/regexconverter/pattern@75.txt
LTLE_TO_AFA=dist-newstyle/build/x86_64-linux/ghc-8.10.7/automata-safa-0.1.0.0/x/ltle-to-afa/opt/build/ltle-to-afa/ltle-to-afa

i=0
cat $REGEX_PATH | while read -r regex; do
  echo "%Section t\"Filter$i\" Regex"
  echo "$regex"
  echo

  echo "%Section t\"Filter$i\" NFA CharRanges"
  $LTLE_TO_AFA range16ToMacheteNfa < ../data/email75/range16nfa/$i
  echo

  echo "%Section t\"Filter$i\" NFA Bits"
  $LTLE_TO_AFA range16ToPretty < ../data/email75/range16nfa/$i | tee /tmp/email-filter-nfa/$i.afa
  echo

  i=$(($i+1))
done
