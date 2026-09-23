#!/usr/bin/env bash
# Build the whole project and fail unless it is error-free, warning-free and sorry-free,
# and every `#print axioms` line lists only the three standard axioms.
set -u
cd "$(dirname "$0")"
lake build 2>&1 | tee build.log
status=${PIPESTATUS[0]}
errors=$(grep -c '^error' build.log || true)
warnings=$(grep -c '^warning' build.log || true)
sorries=$(grep -ci 'sorry' build.log || true)
axioms=$(grep -c 'depends on axioms' build.log || true)
bad_axioms=$(grep 'depends on axioms' build.log | grep -v -c -E '\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]' || true)
echo "lake build exit=$status errors=$errors warnings=$warnings sorry-mentions=$sorries axiom-lines=$axioms nonstandard-axiom-lines=$bad_axioms"
if [ "$status" != "0" ] || [ "$errors" != "0" ] || [ "$warnings" != "0" ] || [ "$sorries" != "0" ] || [ "$bad_axioms" != "0" ] || [ "$axioms" -lt 40 ]; then
  echo "CHECK FAILED"; exit 1
fi
echo "CHECK PASSED: $axioms theorems verified with standard axioms only"
