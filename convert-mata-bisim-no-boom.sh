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

    # TODO: problem, without boomSeparate, states are not in DNF
    $AUTOMATA_SAFA_ONE isSeparated < $f.afa
    if [ $? -eq 0 ]; then
      $AUTOMATA_SAFA_ONE share < $f.afa | $AUTOMATA_SAFA_ONE removeFinalsHind | $AUTOMATA_SAFA_ONE unshare | $AUTOMATA_SAFA_ONE initToDnf | $LTLE_TO_AFA prettyToMachete >> $f.mata 
    else
      $AUTOMATA_SAFA_ONE share < $f.afa | $AUTOMATA_SAFA_ONE delaySymbolsLowest | $AUTOMATA_SAFA_ONE removeFinalsHind | $AUTOMATA_SAFA_ONE unshare | $AUTOMATA_SAFA_ONE initToDnf | $LTLE_TO_AFA prettyToMachete >> $f.mata 
    fi
  }
done
