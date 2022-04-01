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

cabal exec ltle-to-afa range16ToPrettyRangeVars < ../data/email75/range16nfa/0 > playground/0.r.afa
cabal exec ltle-to-afa range16ToPrettyRangeVars < ../data/email75/range16nfa/1 > playground/1.r.afa
cabal exec ltle-to-afa range16ToPrettyRangeVars < ../data/email75/range16nfa/2 > playground/2.r.afa
cabal exec ltle-to-afa range16ToPrettyRangeVars < ../data/email75/range16nfa/3 > playground/3.r.afa
cabal exec ltle-to-afa and playground/0.r.afa playground/1.r.afa playground/2.r.afa playground/3.r.afa > playground/abcd.r.afa
cabal exec ltle-to-afa and playground/0.r.afa playground/1.r.afa playground/2.r.afa playground/3.r.afa playground/3.r.afa > playground/abcdd.r.afa
cabal exec ltle-to-afa negate < playground/abcd.r.afa > playground/abcd-neg.r.afa
cabal exec ltle-to-afa negate < playground/abcdd.r.afa > playground/abcdd-neg.r.afa
cabal exec ltle-to-afa neq playground/abcd.r.afa playground/abcdd.r.afa playground/abcd-neg.r.afa playground/abcdd-neg.r.afa > playground/abcd-abcdd-neq.r.afa

cabal exec ltle-to-afa range16ToPretty < ../dantoni-symbolic/benchmarks/cox-a/5 > playground/cox-a5.afa
cabal exec ltle-to-afa range16ToPretty < ../dantoni-symbolic/benchmarks/cox-b/5 > playground/cox-b5.afa
cabal exec ltle-to-afa negate < playground/cox-b5.afa > playground/cox-b5-neg.afa
cabal exec ltle-to-afa and playground/cox-a5.afa playground/cox-b5-neg.afa > playground/cox-inclusion-unsat5.afa

mkdir -p playground/insimp
mkdir -p playground/outsimp
cp playground/abcd-abcdd-neq.afa playground/insimp/0
cp playground/cox-inclusion-unsat5.afa playground/insimp/1
cabal exec ltle-to-afa -- -i prettyStranger:playground/insimp -o afaBasicSimp:playground/outsimp
cabal exec ltle-to-afa -- -i afa:playground/outsimp -o prettyStranger:playground
rm -r playground/insimp
rm -r playground/outsimp
mv playground/0 playground/abcd-abcdd-neq-basicsimp.afa
mv playground/1 playground/cox-inclusion-unsat5-basicsimp.afa
