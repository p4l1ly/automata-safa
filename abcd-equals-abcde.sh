set -e

echo -e '%Section t"Input regex filter equality." Formula FileSection\n'
echo "%File email-filter-nfa.mata"
echo "%Expression (sFilter$1 & sFilter$2 & sFilter$3 & sFilter$4) == (sFilter$1 & sFilter$2 & sFilter$3 & sFilter$4 & sFilter$5)"

LTLE_TO_AFA=dist-newstyle/build/x86_64-linux/ghc-8.10.7/automata-safa-0.1.0.0/x/ltle-to-afa/noopt/build/ltle-to-afa/ltle-to-afa

$LTLE_TO_AFA and /tmp/email-filter-nfa/$1.afa /tmp/email-filter-nfa/$2.afa /tmp/email-filter-nfa/$3.afa /tmp/email-filter-nfa/$4.afa > /tmp/abcd-equals-abcde/abcd.afa
$LTLE_TO_AFA and /tmp/email-filter-nfa/$1.afa /tmp/email-filter-nfa/$2.afa /tmp/email-filter-nfa/$3.afa /tmp/email-filter-nfa/$4.afa /tmp/email-filter-nfa/$5.afa > /tmp/abcd-equals-abcde/abcde.afa
$LTLE_TO_AFA negate < /tmp/abcd-equals-abcde/abcde.afa > /tmp/abcd-equals-abcde/abcde-neg.afa
$LTLE_TO_AFA and /tmp/abcd-equals-abcde/abcd.afa /tmp/abcd-equals-abcde/abcde-neg.afa > /tmp/abcd-equals-abcde/abcd-abcde-neq.afa
$LTLE_TO_AFA emailFilterBisim /tmp/abcd-equals-abcde/abcd.afa /tmp/email-filter-nfa/$5.afa > /tmp/abcd-equals-abcde/abcd-equals-abcde.bisim

echo -e '\n%Section t"Output AFA." AFA Bits'
$LTLE_TO_AFA prettyToMachete < /tmp/abcd-equals-abcde/abcd-abcde-neq.afa
