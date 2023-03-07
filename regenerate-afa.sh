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
  echo "Processing $j/$NUM_OF_INPUTS: $fAfa" >&2
  let j++
  TMP_DIR=$(mktemp -d)
  $LTLE_TO_AFA parseFormat < "$fAfa" > "$TMP_DIR/tmp.afa"
  mv "$TMP_DIR/tmp.afa" "$fAfa"
  rm -rf $TMP_DIR
done