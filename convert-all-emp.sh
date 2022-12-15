#! /bin/zsh

CONVERT_ONE_EMP="/scripts/convert-one-emp.sh"

if [ -z $1 ]; then
  echo "path argument (where .emp files are) expected" >&2
  exit 1
fi

INPUT_DIR_ABS_PATH=$(echo "$(cd "$(dirname "$1")" && pwd)/$(basename "$1")")

INPUTS=$(find "$INPUT_DIR_ABS_PATH" -type f -name "*.emp")

mkdir createdemps
cd createdemps

TMP=$(echo "$INPUTS" | wc -l)
let NUM_OF_INPUTS=TMP
let j=1
echo $INPUTS | while read -r i; do
	echo "Processing $j/$NUM_OF_INPUTS: ${i}"
	RELATIVE_PATH=${i#"$INPUT_DIR_ABS_PATH"/}
    RELATIVE_PATH=${RELATIVE_PATH%????}
    echo $RELATIVE_PATH
	mkdir -p "$RELATIVE_PATH"
    # CUR_DIR="$(pwd)"
    # zsh $CONVERT_ONE_EMP "$RELATIVE_PATH" <$i
    # cd $CUR_DIR
	let j++
done