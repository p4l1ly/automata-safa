set -ex
rm -rf playground
mkdir playground

cp ../dantoni-symbolic/benchmarks/src/main/java/regexconverter/pattern@75.txt playground/email-filtering.regex

cabal exec ltle-to-afa range16ToPretty < ../data/email75/range16nfa/0 > playground/0.afa
cabal exec ltle-to-afa range16ToPretty < ../data/email75/range16nfa/1 > playground/1.afa
cabal exec ltle-to-afa range16ToPretty < ../data/email75/range16nfa/2 > playground/2.afa
cabal exec ltle-to-afa range16ToPretty < ../data/email75/range16nfa/3 > playground/3.afa
cabal exec ltle-to-afa and playground/0.afa playground/1.afa playground/2.afa playground/3.afa > playground/abcd.afa
cabal exec ltle-to-afa and playground/0.afa playground/1.afa playground/2.afa playground/3.afa playground/3.afa > playground/abcdd.afa
cabal exec ltle-to-afa negate < playground/abcd.afa > playground/abcd-neg.afa
cabal exec ltle-to-afa negate < playground/abcdd.afa > playground/abcdd-neg.afa
cabal exec ltle-to-afa neq playground/abcd.afa playground/abcdd.afa playground/abcd-neg.afa playground/abcdd-neg.afa > playground/abcd-abcdd-neq.afa
cabal exec ltle-to-afa boomSeparate < playground/abcd-abcdd-neq.afa > playground/abcd-abcdd-neq-boomsep.afa
cabal exec ltle-to-afa removeFinals < playground/abcd-abcdd-neq-boomsep.afa > playground/abcd-abcdd-neq-boomsep-nofinals.afa

cabal exec ltle-to-afa range16ToPretty < ../dantoni-symbolic/benchmarks/cox-a/5 > playground/cox-a5.afa
cabal exec ltle-to-afa range16ToPretty < ../dantoni-symbolic/benchmarks/cox-b/5 > playground/cox-b5.afa
cabal exec ltle-to-afa negate < playground/cox-b5.afa > playground/cox-b5-neg.afa
cabal exec ltle-to-afa and playground/cox-a5.afa playground/cox-b5-neg.afa > playground/cox-inclusion-unsat5.afa
cabal exec ltle-to-afa boomSeparate < playground/cox-inclusion-unsat5.afa > playground/cox-inclusion-unsat5-boomsep.afa
cabal exec ltle-to-afa removeFinals < playground/cox-inclusion-unsat5-boomsep.afa > playground/cox-inclusion-unsat5-boomsep-nofinals.afa

mkdir -p playground/insimp
mkdir -p playground/outsimp
cp playground/abcd-abcdd-neq-boomsep-nofinals.afa playground/insimp/0
cp playground/cox-inclusion-unsat5-boomsep-nofinals.afa playground/insimp/1
cabal exec ltle-to-afa -- -i prettyStranger:playground/insimp -o afaBasicSimp:playground/outsimp
rm -r playground/insimp
cabal exec ltle-to-afa -- -i afa:playground/outsimp -o prettyStranger:playground
rm -r playground/outsimp
mv playground/0 playground/abcd-abcdd-neq-boomsep-nofinals-basicsimp.afa
mv playground/1 playground/cox-inclusion-unsat5-boomsep-nofinals-basicsimp.afa

cabal exec ltle-to-afa qdnf < playground/abcd-abcdd-neq-boomsep-nofinals-basicsimp.afa > playground/abcd-abcdd-neq-boomsep-nofinals-basicsimp-qdnf.afa
cabal exec ltle-to-afa qdnf < playground/cox-inclusion-unsat5-boomsep-nofinals-basicsimp.afa > playground/cox-inclusion-unsat5-boomsep-nofinals-basicsimp-qdnf.afa

mkdir -p playground/insimp
mkdir -p playground/outsimp
cp playground/abcd-abcdd-neq-boomsep-nofinals-basicsimp-qdnf.afa playground/insimp/0
cp playground/cox-inclusion-unsat5-boomsep-nofinals-basicsimp-qdnf.afa playground/insimp/1
cabal exec ltle-to-afa -- -i prettyStranger:playground/insimp -o afaBasicSimp:playground/outsimp
rm -r playground/insimp
cabal exec ltle-to-afa -- -i afa:playground/outsimp -o prettyStranger:playground
rm -r playground/outsimp
mv playground/0 playground/abcd-abcdd-neq-boomsep-nofinals-basicsimp-qdnf-basicsimp.afa
mv playground/1 playground/cox-inclusion-unsat5-boomsep-nofinals-basicsimp-qdnf-basicsimp.afa

cabal exec ltle-to-afa treeRepr < playground/abcd-abcdd-neq-boomsep-nofinals-basicsimp-qdnf-basicsimp.afa | grep -v '^@s0' | sed 's/!s0 & //' > playground/abcd-abcdd-neq-boomsep-nofinals-basicsimp-qdnf-basicsimp-tree.afa
cabal exec ltle-to-afa treeRepr < playground/cox-inclusion-unsat5-boomsep-nofinals-basicsimp-qdnf-basicsimp.afa | grep -v '^@s0' | sed 's/!s0 & //' > playground/cox-inclusion-unsat5-boomsep-nofinals-basicsimp-qdnf-basicsimp-tree.afa
