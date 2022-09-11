[ -z $1 ] && { echo path argument expected >&2; exit 1 }

UUID=$(uuidgen)
TIMEOUT=20
TIMEOUT_MS=20000

mkdir /tmp/afasat-$UUID
mkdir /tmp/bisim-$UUID

find $1 -name '*.afa' | while read -r fAfa; do
  f=${fAfa%????}
  ffull=$PWD/$f
  echo Processing $f >&2

  ${Abc:-false} && {
    cd ../abc
    tic=$(date +"%s.%N")
    timeout $TIMEOUT /usr/bin/time -f "%e" ./build/abc -c "read_aiger $ffull.aig; drw; rf; b; drw; rwz; b; rfz; rwz; b; pdr -T $TIMEOUT" > /tmp/abc.result.$UUID 2> /tmp/abc.time.$UUID
    result=$?
    {
      echo -n -e "abc\t$f\t"
      if [ $result = 124 ]; then
        echo -e "$TIMEOUT_MS\t-2"
      elif [ $result = 134 ]; then
        echo -e "$(python3 -c 'import sys; print(float(sys.argv[1]) * 1000)' $(($(date +'%s.%N')-$tic)))\t-3"
      else
        echo -n -e "$(($(cat /tmp/abc.time.$UUID)*1000))\t"
        if cat /tmp/abc.result.$UUID | grep Output > /dev/null; then
          echo 1
        elif cat /tmp/abc.result.$UUID | grep prove > /dev/null; then
          echo 0
        else
          echo -4
        fi
      fi
    }
    cd -
  }

  ${Mona:-false} && {
    tic=$(date +"%s.%N")
    timeout $TIMEOUT /usr/bin/time -f "%e" ../mona-1.4/Front/mona $f.mona > /tmp/mona.result.$UUID 2> /tmp/mona.time.$UUID
    result=$?
    {
      echo -n -e "mona\t$f\t"
      if [ $result = 124 ]; then
        echo -e "$TIMEOUT_MS\t-2"
      elif [ $result = 134 ]; then
        echo -e "$(python3 -c 'import sys; print(float(sys.argv[1]) * 1000)' $(($(date +'%s.%N')-$tic)))\t-3"
      else
        echo -n -e "$(python3 -c 'import sys; print(float(sys.argv[1]) * 1000)' $(cat /tmp/mona.time.$UUID))\t"
        if cat /tmp/mona.result.$UUID | grep 'A satisfying example' > /dev/null; then
          echo 1
        elif cat /tmp/mona.result.$UUID | grep unsatisfiable > /dev/null; then
          echo 0
        else
          echo -4
          echo $result
          cat /tmp/mona.time.$UUID
        fi
      fi
    }
  }

  ${Afasat:-false} && {
    cp $f.afasat /tmp/afasat-$UUID/0
    ../afapipe/build/file-solver-2 /tmp/afasat-$UUID | sed 's/^0//' | awk "{print \"afasat\\t$f\" \$0}"
  }

  ${Bisim:-false} && {
    cp $f.bisim /tmp/bisim-$UUID/0
    ../afapipe/build/file-solver-1 /tmp/bisim-$UUID | sed 's/^0//' | awk "{print \"bisim\\t$f\" \$0}"
  }
done
