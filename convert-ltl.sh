LTLE_TO_AFA=ltle-to-afa
SMVTOAIG=~/aiger/smvtoaig

if [ -z $1 ]; then
  echo "path argument expected" >&2
  exit 1
fi

if [ -f $1 ]; then
  echo $1
else
  find $1 -name '*.pltl' -or -name '*.ltlf'
fi | while read -r ltl; do
  f=${ltl%?????}
  ext=${ltl:(-4)}
  echo Processing $ltl >&2
  cat $ltl | ltl-translators-exe $ext | $LTLE_TO_AFA -i ltl -o prettyStranger:/tmp/
  mv /tmp/0 $f.afa
done
