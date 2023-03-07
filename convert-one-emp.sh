#! /bin/zsh

LTLE_TO_AFA=ltle-to-afa
CONVERT_FOR_CHECKERS="/scripts/convert-for-checkers.sh"
BRICSREG=~/emptiness-brics/target/regex-parser.jar

if [ -z $1 ]; then
  echo "path argument (where created automata are saved) expected" >&2
  exit 1
fi

WORKDIR=$(realpath "$1")
GEN_AUT_DIR="$WORKDIR/gen_aut"
# rm -rf "$GEN_AUT_DIR"
rm "$WORKDIR/result.emp"
LOGFILE="$WORKDIR/log"
rm "$LOGFILE"
mkdir "$GEN_AUT_DIR"

while IFS= read -r line; do
  echo "$line"
  echo "$line" >> $LOGFILE
  if grep '^load_regex' <<< "$line" > /dev/null; then
    operands=${line#* }
    name=$(sed -r 's/^load_regex ([^ ]+) .*/\1/' <<< "$line")
    regex=$(sed -r 's/^load_regex [^ ]+ //' <<< "$line")

    echo "load_automaton $name" >> "$WORKDIR/result.emp"

    java -jar $BRICSREG $GEN_AUT_DIR/$name.range16nfa <<< "$regex" >>$LOGFILE 2>&1
    $LTLE_TO_AFA range16ToPretty < $GEN_AUT_DIR/$name.range16nfa > $GEN_AUT_DIR/$name.afa 2>>$LOGFILE

    echo "@NFA-bits" > $GEN_AUT_DIR/$name.mata
    $LTLE_TO_AFA prettyToSeparatedMata < $GEN_AUT_DIR/$name.afa >> $GEN_AUT_DIR/$name.mata 2>>$LOGFILE
    echo "@NFA-bits" > $GEN_AUT_DIR/"$name"_mona.mata
    $LTLE_TO_AFA prettyToSeparatedDnfMata < $GEN_AUT_DIR/$name.afa >> $GEN_AUT_DIR/"$name"_mona.mata 2>>$LOGFILE

  elif grep '^load_automaton' <<< "$line" > /dev/null; then 
    name=$(sed -r 's/^load_automaton //' <<< "$line")
    echo "load_automaton $name" >> "$WORKDIR/result.emp"

  elif grep '=' <<< "$line" > /dev/null; then
    name=$(sed -r 's/^([^ ]+) .*/\1/' <<< "$line")
    operator=$(sed -r 's/^[^ ]+ = \(([^ ]+) .*/\1/' <<< "$line")
    operands=($(sed -r 's/^[^ ]+ = \([^ ]+ (.*)\)/\1/' <<< "$line"))
    operands2=(${${operands[@]/%/.afa}/#/$GEN_AUT_DIR/})

    echo "$line" >> "$WORKDIR/result.emp"

    case $operator in
      compl) $LTLE_TO_AFA negate < ${operands2[1]} > $GEN_AUT_DIR/$name.afa 2>>$LOGFILE;;
      inter) $LTLE_TO_AFA and $operands2 > $GEN_AUT_DIR/$name.afa 2>>$LOGFILE;;
      union) $LTLE_TO_AFA or $operands2 > $GEN_AUT_DIR/$name.afa 2>>$LOGFILE;;
    esac

  elif grep '^is_empty' <<< "$line" > /dev/null; then
    name=$(sed -r 's/^is_empty //' <<< "$line")

    echo "$line" >> "$WORKDIR/result.emp"

    cp $GEN_AUT_DIR/$name.afa $WORKDIR/result.afa
    
    # export Ada=true
    # export Aiger=true
    # export Bisim=true
    # export Afasat=true
    # export Mata=true
    # zsh "$CONVERT_FOR_CHECKERS" $WORKDIR/result.afa >>$LOGFILE 2>&1
  elif grep '^incl' <<< "$line" > /dev/null; then
    echo "$line" >> "$WORKDIR/result.emp"

    operands=($(sed -r 's/^incl //' <<< "$line"))
    operands2=(${${operands[@]/%/.afa}/#/$GEN_AUT_DIR/})

    $LTLE_TO_AFA negate < ${operands2[2]} > $GEN_AUT_DIR/${operands[2]}_neg.afa 2>>$LOGFILE
    $LTLE_TO_AFA and ${operands2[1]} $GEN_AUT_DIR/${operands[2]}_neg.afa > $WORKDIR/result.afa 2>>$LOGFILE
  fi
done
