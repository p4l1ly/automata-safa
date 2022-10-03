set -e
rm -rf /tmp/stranger
mkdir /tmp/stranger

LTLE_TO_AFA=dist-newstyle/build/x86_64-linux/ghc-8.10.7/automata-safa-0.1.0.0/x/ltle-to-afa/opt/build/ltle-to-afa/ltle-to-afa

for f in $(ls ../data/stranger/input/ | sort -n); do
  echo $f
  echo '@AFA-bits' > /tmp/stranger/$f.mata
  $LTLE_TO_AFA strangerToMachete < ../data/stranger/input/$f >> /tmp/stranger/$f.mata
  $LTLE_TO_AFA strangerToPretty < ../data/stranger/input/$f >> /tmp/stranger/$f.afa
done
