LTLE_TO_AFA=dist-newstyle/build/x86_64-linux/ghc-8.10.7/automata-safa-0.1.0.0/x/ltle-to-afa/noopt/build/ltle-to-afa/ltle-to-afa
SMVTOAIG=../aiger/smvtoaig

[ -z $1 ] && { echo path argument expected >&2; exit 1 }

if [ -f $1 ]; then
  echo $1
else
  find $1 -name '*.afa'
fi | while read -r fAfa; do
  f=${fAfa%????}
  echo Processing $f >&2
  ${Mata:-false} && {
    echo "%Section AFA Bits" > $f.mata
    $LTLE_TO_AFA prettyToMachete < $f.afa >> $f.mata
  }
  ${Smv:-false} && $LTLE_TO_AFA prettyToSmv < $f.afa > $f.smv
  ${Aiger:-false} && $SMVTOAIG $f.smv > $f.aig
  ${Mona:-false} && $LTLE_TO_AFA prettyToMona < $f.afa > $f.mona
  ${Afasat:-false} &&
    $LTLE_TO_AFA removeFinalsNonsep < $f.afa | $LTLE_TO_AFA prettyToAfasat > $f.afasat
  ${Ada:-false} && {
    $LTLE_TO_AFA prettyToAda < $f.afa > $f.ada 2> /dev/null || \
    $LTLE_TO_AFA removeFinalsNonsep < $f.afa | $LTLE_TO_AFA prettyToAda > $f.ada
  }
done
