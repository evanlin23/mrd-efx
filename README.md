# Strong EFX₀ for 2-relevant agents — Lean 4 formalization

Formal companion to the paper *Strong EFX Allocations Exist When Every Agent Values at Most Two
Goods* (Evan Lin and Gerald Osterhaus, 2026). Every result of the paper is proved in core Lean 4
(no Mathlib), including the executable algorithms.

Toolchain: **leanprover/lean4:v4.34.0**, pinned in `lean-toolchain`; `elan` installs it on first
use. The development builds with no errors and no warnings. The complete build log from a fresh
checkout is `BUILDLOG-lean-4.34.0.txt`; its `#print axioms` lines are the certificate that no
theorem depends on `sorryAx` or on any non-standard axiom. Deprecated names are avoided (`ifp`/`ifn`
replace `if_pos`/`if_neg`).

## Build and audit

    # install elan once: https://github.com/leanprover/elan
    ./check.sh            # build + audit: any error, warning, sorry or non-standard axiom fails

On success the last line is `CHECK PASSED: 40 theorems verified with standard axioms only`, and
every `#print axioms` line above it lists only `propext`, `Classical.choice` and `Quot.sound`. No
file contains `sorry`. The GitHub Actions workflow in `.github/workflows/lean.yml` runs the same
audit on every push, followed by the native random test:

    lake build            # builds the four modules and prints the `#print axioms` lines
    lake build mrdtest    # native random-test driver
    lake exe mrdtest 20000 12 12 7   # trials, max agents, max goods, seed

## Contents

* `MRD.lean` — additive model. Main theorems: `MRD.main_theorem_L` (existence + shape under
  |R_i| <= 2, via `MRD.mrdL_efx0`: greedy, then every unassigned good goes to the last agent, who is
  always a source by `MRD.lastAgent_source_all`), `MRD.main_theorem`/`MRD.mrdG_efx0` (the variant that
  prefers an unassigned agent as the sink), `MRD.mrd_correct` (rotation-based variant: sound and live),
  `MRD.efx0_of_invariants` (tie-breaking independence), `MRD.efx0Check_iff` (sound and complete
  checker), `MRD.mrdA_eq`/`MRD.mrdGA_eq` (array-backed executables equal the specifications).
* `MRDMono.lean` — general monotone valuations on at most two goods (substitutes, complements, ...).
  Main theorems: `MRDM.mrdML_efx0`/`MRDM.main_theorem_L` (last agent is the sink) and
  `MRDM.mrdM_efx0`/`MRDM.main_theorem` (unassigned agent preferred). Kernel-checked example
  `MRDM.exM_ok` with a complementary agent.
* `MRDBridge.lean` — embeds every 2-relevant additive instance into the monotone model and proves
  the two `EFX0` predicates coincide (`MRDBridge.efx0_iff`); hence the additive theorem is a
  corollary of the monotone one (`MRDBridge.additive_via_monotone`).
* `MRDDeg3.lean` — the degree-3 sharpness example: exactly two of the sixteen allocations are
  strongly EFX₀ (`MRDDeg3.sharp`), kernel-checked through the complete checker; no EFX₀ allocation
  has all bundles but one of size ≤ 1 (`MRDDeg3.no_thin_shape`), and every EFX₀ allocation gives
  some agent two of its relevant goods (`MRDDeg3.two_relevant_goods`).
* `MRDTest.lean` — native driver running both verified executables on random instances.
## Correspondence with the paper

| Statement in the paper | Lean (file : name) |
|---|---|
| Local characterization lemma (as used) | MRD : `PAssign.other_val`, `own_val`, `sink_val_le` |
| Invariants (P1)–(P3) of Phase 1 | MRD : `phase1_inv`, `phase1_later`, `phase1_holders` |
| The envy digraph is acyclic; the last agent is always a source | MRD : `succE_lt`, `findCycle_phase1`, `lastAgent_source_all` |
| The dump bundle is thin | MRD : `PAssign.thin_dump`, `PAssign.dump_bound` |
| Main theorem (additive) | MRD : `mrdL_efx0`, `mrdL_shape`, `main_theorem_L` |
| Variant preferring an unassigned sink | MRD : `mrdG_efx0`, `mrdGA_eq`, `main_theorem` |
| Any source may be the sink | MRD : `PAssign.dump_efx0`, `efx0_of_invariants` |
| Tie-breaking independence | MRD : `efx0_of_invariants` |
| Existence under \|R_i\| ≤ 2 | MRD : `twoRelevant_of_count`, `exists_efx0_of_count` |
| Monotone invariants and main theorem | MRDMono : `phase1Upto_inv`, `PA.dump_efx0`, `mrdML_efx0`, `main_theorem_L` |
| Additive theorem as a corollary of the monotone one | MRDBridge : `efx0_iff`, `additive_via_monotone` |
| Checker soundness and completeness | MRD : `efx0Check_iff` |
| Degree-3 sharpness example | MRDDeg3 : `sharp`, `no_thin_shape`, `two_relevant_goods` |

Not formalized: the running-time bound O(n+m) (a statement about the algorithm with array
bookkeeping; the Lean executables use quadratic search helpers), and real-valued utilities (values
are natural numbers in Lean; the argument is order-theoretic and applies verbatim to nonnegative
reals).

## Citing and license

Apache-2.0 (see `LICENSE`). Citation metadata is in `CITATION.cff`; the release corresponding to
the paper is tag `v1.1.0`.
