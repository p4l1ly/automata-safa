LTLE_TO_AFA=dist-newstyle/build/x86_64-linux/ghc-8.10.7/automata-safa-0.1.0.0/x/ltle-to-afa/opt/build/ltle-to-afa/ltle-to-afa
SMVTOAIG=../aiger/smvtoaig

[ -z $1 ] && { echo path argument expected >&2; exit 1 }

find $1 -name '*.afa' | while read -r fAfa; do
  f=${fAfa%????}
  echo Processing $f >&2
  ${Mata:-false} && {
    echo "%Section AFA Bits" > $f.mata
    $LTLE_TO_AFA prettyToMachete < $f.afa >> $f.mata
  }
  ${Smv:-false} && $LTLE_TO_AFA prettyToSmv < $f.afa > $f.smv
  ${Aiger:-false} && $SMVTOAIG $f.smv > $f.aig
  ${Mona:-false} && $LTLE_TO_AFA prettyToMona < $f.afa > $f.mona
  ${Afasat:-false} && $LTLE_TO_AFA prettyToAfasat < $f.afa > $f.afasat
done
