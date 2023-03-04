LTLE_TO_AFA=ltle-to-afa
AUTOMATA_SAFA_ONE=automata-safa-one
SMVTOAIG=~/aiger/smvtoaig
SEPARATED=~/automata-safa-capnp/schema/Afa/Model/Separated.capnp

if [ -z $1 ]; then
  echo "path argument (to directory containing .afa files or to some .afa file) expected" >&2
  exit 1
fi

afa_names="*"
if [[ ! -z $2 ]]; then
  afa_names="$2"
fi

if [ -f $1 ]; then
  echo $1
  let NUM_OF_INPUTS=1
else
  TMP=$(find $1 -name "$afa_names.afa" | wc -l)
  let NUM_OF_INPUTS=TMP
fi 

let j=1
if [ -f $1 ]; then
  echo $1
else
  find $1 -name "$afa_names.afa"
fi | while read -r fAfa; do
  f=${fAfa%????}
  echo "Processing $j/$NUM_OF_INPUTS: $f" >&2
  let j++
  ${Mata:-false} && {
    echo "Transforming to .mata"
    echo "@AFA-bits" > $f.mata
    # TODO: is this pipe correct? especially treeRepr? what is treeReprUninit?
    $LTLE_TO_AFA boomSeparate < $f.afa | $LTLE_TO_AFA removeFinals | $LTLE_TO_AFA treeRepr | $LTLE_TO_AFA initToDnf | $LTLE_TO_AFA prettyToMachete >> $f.mata
  }
  ${Aiger:-false} && {
    echo "Transforming to .aig"
    TMP_DIR=$(mktemp -d)
    $AUTOMATA_SAFA_ONE share < $f.afa | $AUTOMATA_SAFA_ONE removeUselessShares > "$TMP_DIR/afa.afa"
    if $AUTOMATA_SAFA_ONE hasComplexFinals < "$TMP_DIR/afa.afa"; then
      $AUTOMATA_SAFA_ONE removeFinals < "$TMP_DIR/afa.afa" | $LTLE_TO_AFA prettyToSmv | $SMVTOAIG > $f.aig
    else
      $LTLE_TO_AFA prettyToSmv < "$TMP_DIR/afa.afa" | $SMVTOAIG > $f.aig
    fi
    rm -rf $TMP_DIR
  }
  ${Mona:-false} && {
    echo "Transforming to .mona"
    $LTLE_TO_AFA prettyToMona < $f.afa > $f.mona
  }
  ${Afasat:-false} && {
    echo "Transforming to .afasat"
    $LTLE_TO_AFA removeFinalsNonsep < $f.afa | $LTLE_TO_AFA prettyToAfasat > $f.afasat
  }
  ${Ada:-false} && {
    echo "Transforming to .ada"
    $LTLE_TO_AFA prettyToAda < $f.afa > $f.ada 2> /dev/null || \
    $LTLE_TO_AFA removeFinalsNonsep < $f.afa | $LTLE_TO_AFA prettyToAda > $f.ada
  }
  ${Bisim:-false} && {
    echo "Transforming to .bisim"
    TMP_DIR=$(mktemp -d)
    $LTLE_TO_AFA boomSeparate < $f.afa | $LTLE_TO_AFA removeFinals > "$TMP_DIR/0"
    echo "@kInitialFormula: s0
@kFinalFormula: !s0
@s0: kFalse" > "$TMP_DIR/1"
    $LTLE_TO_AFA eqBisim "$TMP_DIR/0" "$TMP_DIR/1" | capnp convert binary:text $SEPARATED TwoBoolAfas | capnp convert text:binary $SEPARATED TwoBoolAfas > $f.bisim
    rm -rf $TMP_DIR
  }
done
