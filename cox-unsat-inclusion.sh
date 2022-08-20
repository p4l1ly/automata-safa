set -e
rm -rf /tmp/cox-unsat-inclusion
mkdir /tmp/cox-unsat-inclusion

LTLE_TO_AFA=dist-newstyle/build/x86_64-linux/ghc-8.10.7/automata-safa-0.1.0.0/x/ltle-to-afa/opt/build/ltle-to-afa/ltle-to-afa

for i in 2 3 4 6 10 16 25 40 63 100 158 251 398 631 1000; do
  $LTLE_TO_AFA range16ToPretty < ../dantoni-symbolic/benchmarks/cox-c/$i > /tmp/cox-unsat-inclusion/a.afa
  $LTLE_TO_AFA range16ToPretty < ../dantoni-symbolic/benchmarks/cox-d/$i > /tmp/cox-unsat-inclusion/b.afa
  $LTLE_TO_AFA negate < /tmp/cox-unsat-inclusion/b.afa > /tmp/cox-unsat-inclusion/b-neg.afa
  $LTLE_TO_AFA and /tmp/cox-unsat-inclusion/a.afa /tmp/cox-unsat-inclusion/b-neg.afa > /tmp/cox-unsat-inclusion/$i.afa
  echo '%Section AFA Bits' > /tmp/cox-unsat-inclusion/$i.mata
  $LTLE_TO_AFA prettyToMachete < /tmp/cox-unsat-inclusion/$i.afa >> /tmp/cox-unsat-inclusion/$i.mata
done

rm /tmp/cox-unsat-inclusion/a.afa
rm /tmp/cox-unsat-inclusion/b.afa
rm /tmp/cox-unsat-inclusion/b-neg.afa
