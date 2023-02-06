#! /bin/zsh

DANTONI=~/symbolicautomata/benchmarks
LTLE_TO_AFA=ltle-to-afa
CONVERT_FOR_CHECKERS="/scripts/convert-for-checkers.sh"

if [ -z $1 ]; then
  echo "path argument (where created automata are saved) expected" >&2
  exit 1
fi

rm -rf $DANTONI/regexNfas
mkdir $DANTONI/regexNfas

WORKDIR=$(realpath "$1")
GEN_AUT_DIR="$WORKDIR/gen_aut"
LOGFILE="$WORKDIR/log"
mkdir "$GEN_AUT_DIR"

while IFS= read -r line; do
  echo "$line"
  echo "$line" >> $LOGFILE
  if grep '^load_regex' <<< "$line" > /dev/null; then
    operands=${line#* }
    name=$(sed -r 's/^load_regex ([^ ]+) .*/\1/' <<< "$line")
    regex=$(sed -r 's/^load_regex [^ ]+ //' <<< "$line")

    echo "load_automaton $name" >> "$WORKDIR/result.emp"

    if [ -z "$regex" ]; then
      echo "@kInitialFormula: s0
@kFinalFormula: !s0
@s0: kFalse" > $GEN_AUT_DIR/$name.afa
    else 
      cd $DANTONI
      zsh runtutor <<< "$regex" >>$LOGFILE 2>&1
      cd -
      cp $DANTONI/regexNfas/0 $GEN_AUT_DIR/$name.range16nfa 2>>$LOGFILE
      $LTLE_TO_AFA range16ToPretty < $GEN_AUT_DIR/$name.range16nfa > $GEN_AUT_DIR/$name.afa 2>>$LOGFILE
      # echo "@NFA-intervals" > $GEN_AUT_DIR/$name-ranges.mata
      # echo "%Alphabet chars" >> $GEN_AUT_DIR/$name-ranges.mata
      # $LTLE_TO_AFA range16ToMacheteNfa < $GEN_AUT_DIR/$name.range16nfa >> $GEN_AUT_DIR/$name-ranges.mata 2>/dev/null
    fi
    echo "@NFA-bits" > $GEN_AUT_DIR/$name.mata
    $LTLE_TO_AFA prettyToSeparatedMata < $GEN_AUT_DIR/$name.afa >> $GEN_AUT_DIR/$name.mata 2>>$LOGFILE
    echo "@NFA-bits" > $GEN_AUT_DIR/"$name"_mona.mata
    $LTLE_TO_AFA prettyToSeparatedDnfMata < $GEN_AUT_DIR/$name.afa >> $GEN_AUT_DIR/"$name"_mona.mata 2>>$LOGFILE
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
  fi
done
