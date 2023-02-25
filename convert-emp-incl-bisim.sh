#! /bin/zsh

LTLE_TO_AFA=ltle-to-afa
SEPARATED=~/automata-safa-capnp/schema/Afa/Model/Separated.capnp

if [ -z $1 ]; then
  echo "path argument (to directory containing .afa files or to some .afa file) expected" >&2
  exit 1
fi

emp_name="result.emp"

if [ -f $1 ]; then
  echo $1
  let NUM_OF_INPUTS=1
else
  TMP=$(find $1 -name "$emp_name" | wc -l)
  let NUM_OF_INPUTS=TMP
fi 

let j=1
if [ -f $1 ]; then
  echo $1
else
  find $1 -name "$emp_name"
fi | while read -r empFile; do
  f=${empFile%????}
  WORKDIR=$(dirname $(realpath "$empFile"))
  GEN_AUT_DIR="$WORKDIR/gen_aut"
  echo "Processing $j/$NUM_OF_INPUTS: $f" >&2
  let j++

  cat $empFile | while IFS= read -r line; do
    if grep '^incl' <<< "$line" > /dev/null; then

      operands=($(sed -r 's/^incl //' <<< "$line"))
      operands2=(${${operands[@]/%/.afa}/#/$GEN_AUT_DIR/})

      TMP_DIR=$(mktemp -d)

      $LTLE_TO_AFA and $operands2 > "$TMP_DIR/0"

      $LTLE_TO_AFA eqBisim ${operands2[1]} "$TMP_DIR/0" | capnp convert binary:text $SEPARATED TwoBoolAfas | capnp convert text:binary $SEPARATED TwoBoolAfas > $f.bisim

      rm -rf $TMP_DIR
    fi
  done
done