#! /bin/zsh

DANTONI=../dantoni-symbolic/benchmarks
LTLE_TO_AFA=dist-newstyle/build/x86_64-linux/ghc-8.10.7/automata-safa-0.1.0.0/x/ltle-to-afa/noopt/build/ltle-to-afa/ltle-to-afa
UUID=${UUID:-$(uuidgen)}

WORKDIR=/tmp/convert-ere-$UUID

rm -rf $WORKDIR
mkdir $WORKDIR
rm $DANTONI/regexNfas/*

while read -r line; do
  if grep '^load_regex' <<< "$line" > /dev/null; then
    name=$(sed -r 's/^load_regex ([^ ]+) .*/\1/' <<< "$line")
    regex=$(sed -r 's/^load_regex [^ ]+ //' <<< "$line")

    echo load
    echo name "$name"
    echo regex "$regex"
    echo

    cd $DANTONI
    zsh runtutor <<< "$regex"
    cd -
    cp $DANTONI/regexNfas/0 $WORKDIR/$name.range16nfa
    $LTLE_TO_AFA range16ToPretty < $WORKDIR/$name.range16nfa > $WORKDIR/$name.afa
  elif grep '=' <<< "$line" > /dev/null; then
    name=$(sed -r 's/^([^ ]+) .*/\1/' <<< "$line")
    operator=$(sed -r 's/^[^ ]+ = \(([^ ]+) .*/\1/' <<< "$line")
    operands=($(sed -r 's/^[^ ]+ = \([^ ]+ (.*)\)/\1/' <<< "$line"))
    operands2=(${${operands[@]/%/.afa}/#/$WORKDIR/})

    echo assign
    echo name "$name"
    echo operator "$operator"
    echo operands "$operands2"
    echo

    case $operator in
      compl) $LTLE_TO_AFA negate < ${operands2[1]} > $WORKDIR/$name.afa;;
      inter) $LTLE_TO_AFA and $operands2 > $WORKDIR/$name.afa;;
      union) $LTLE_TO_AFA or $operands2 > $WORKDIR/$name.afa;;
    esac

  elif grep '^is_empty' <<< "$line" > /dev/null; then
    name=$(sed -r 's/^is_empty //' <<< "$line")

    echo out
    echo name "$name"
    echo

    cp $WORKDIR/$name.afa $WORKDIR/result.afa
  fi
done
