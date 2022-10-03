set -e
rm -rf /tmp/email-filter-nfa
mkdir /tmp/email-filter-nfa

REGEX_PATH=../dantoni-symbolic/benchmarks/src/main/java/regexconverter/pattern@75.txt
LTLE_TO_AFA=dist-newstyle/build/x86_64-linux/ghc-8.10.7/automata-safa-0.1.0.0/x/ltle-to-afa/noopt/build/ltle-to-afa/ltle-to-afa

i=0
cat $REGEX_PATH | while read -r regex; do
  echo "@Regex t\"Filter$i\""
  echo "%Main $regex"
  echo

  echo "@NFA-intervals t\"Filter$i\""
  echo "%Alphabet chars"
  $LTLE_TO_AFA range16ToMacheteNfa < ../data/email75/range16nfa/$i
  echo

  echo "@NFA-bits t\"Filter$i\""
  $LTLE_TO_AFA range16ToPretty < ../data/email75/range16nfa/$i > /tmp/email-filter-nfa/$i.afa
  $LTLE_TO_AFA prettyToSeparatedMata < /tmp/email-filter-nfa/$i.afa
  echo

  echo "@NFA-bits t\"Filter$i\" t\"%DNF\""
  $LTLE_TO_AFA prettyToSeparatedDnfMata < /tmp/email-filter-nfa/$i.afa
  echo

  cp ../data/email75/range16nfa/$i /tmp/email-filter-nfa/$i.nfa

  i=$(($i+1))
done
