#!/usr/bin/env bash
# Build the whole project and fail unless: no source file contains the word `sorry`; the build is
# error-free and warning-free; every `#print axioms` certificate lists only the three standard
# axioms; and the number of certificates equals the number of `#print axioms` commands in the
# sources.
set -u
cd "$(dirname "$0")"
if grep -n 'sorry' ./*.lean; then
  echo "CHECK FAILED: the word 'sorry' occurs in a source file"; exit 1
fi
lake build 2>&1 | tee build.log
status=${PIPESTATUS[0]}
errors=$(grep -c '^error' build.log || true)
warnings=$(grep -c '^warning' build.log || true)
sorries=$(grep -ci 'sorry' build.log || true)
axioms=$(grep -c 'depends on axioms' build.log || true)
expected=$(cat ./*.lean | grep -c '^#print axioms' || true)
theorems=$(cat ./*.lean | grep -cE '^[[:space:]]*(private |protected )?theorem ' || true)
bad_axioms=$(grep 'depends on axioms' build.log | grep -v -c -E '\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]' || true)
echo "lake build exit=$status errors=$errors warnings=$warnings sorry-mentions=$sorries axiom-lines=$axioms expected=$expected nonstandard-axiom-lines=$bad_axioms theorems=$theorems"
if [ "$status" != "0" ] || [ "$errors" != "0" ] || [ "$warnings" != "0" ] || [ "$sorries" != "0" ] || [ "$bad_axioms" != "0" ] || [ "$axioms" != "$expected" ]; then
  echo "CHECK FAILED"; exit 1
fi
echo "CHECK PASSED: $axioms audited statements, $theorems theorems, standard axioms only"
