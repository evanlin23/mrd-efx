# Strong EFX_0 for 2-relevant agents — Lean 4 verification

Core Lean 4 only (no Mathlib). Toolchain pinned in `lean-toolchain`: **leanprover/lean4:v4.19.0**.
Verified to build unchanged, with **no errors and no warnings**, on **v4.19.0**, **v4.27.0** and
**v4.34.0** (the newest release at the time of writing), each time from a fresh unzip of this archive.
The full build logs are included: `BUILDLOG-lean-4.19.0.txt`, `BUILDLOG-lean-4.27.0.txt`,
`BUILDLOG-lean-4.34.0.txt`. To build with another version, edit `lean-toolchain`; nothing else depends
on the version. Deprecated names are avoided (`ifp`/`ifn` replace `if_pos`/`if_neg`).

## Citing and license

Apache-2.0 (see `LICENSE`). Citation metadata is in `CITATION.cff`; the tagged release corresponding
to the paper is `v1.0.0`, and the `#print axioms` lines of its build logs are the certificate that
no theorem depends on `sorryAx` or on any non-standard axiom.

## Build and audit

    ./check.sh            # lake build + audit: fails on any error, warning, `sorry`, or non-standard axiom

A GitHub Actions workflow (`.github/workflows/lean.yml`) runs the same audit on Lean 4.19.0 and 4.34.0.

## Build

    # install elan once: https://github.com/leanprover/elan
    lake build            # builds MRD.lean and MRDMono.lean; prints `#print axioms` lines
    lake build mrdtest    # native random-test driver
    lake exe mrdtest 20000 12 12 7   # trials, max agents, max goods, seed

The build must report no errors. Every `#print axioms` line must list only
`propext`, `Classical.choice`, `Quot.sound` — never `sorryAx`. Neither file contains `sorry`.

## Contents

* `MRD.lean` — additive model. Main theorems: `MRD.main_theorem` (existence + shape under |R_i| <= 2),
  `MRD.mrdG_efx0` (simplified algorithm: greedy, then dump on an unassigned agent or else the last agent),
  `MRD.mrd_correct` (rotation-based variant: sound and live), `MRD.efx0_of_invariants` (tie-breaking
  independence), `MRD.efx0Check_iff` (sound and complete checker), `MRD.mrdA_eq`/`MRD.mrdGA_eq`
  (array-backed executables equal the specifications).
* `MRDMono.lean` — general monotone valuations on at most two goods (substitutes, complements, ...).
  Main theorem: `MRDM.mrdM_efx0`. Kernel-checked example `MRDM.exM_ok` with a complementary agent.
* `MRDBridge.lean` — embeds every 2-relevant additive instance into the monotone model and proves the two
  `EFX0` predicates coincide (`MRDBridge.efx0_iff`); hence the additive theorem is a corollary of the monotone
  one (`MRDBridge.additive_via_monotone`).
* `MRDDeg3.lean` — the degree-3 sharpness example: exactly two of the sixteen allocations are strongly EFX₀
  (`MRDDeg3.sharp`), kernel-checked through the complete checker; no EFX₀ allocation has all bundles but one
  of size ≤ 1 (`MRDDeg3.no_thin_shape`), and every EFX₀ allocation gives some agent two of its relevant goods
  (`MRDDeg3.two_relevant_goods`).
* `MRDTest.lean` — native driver running both verified executables on random instances.

## Traceability: write-up claim → Lean theorem → test evidence

| Claim in the write-up | Lean (file : name) | Test evidence |
|---|---|---|
| Lemma 1 (local EFX₀ test) | MRD : `PAssign.other_val`, `own_val`, `sink_val_le` (used in place of the general lemma) | — |
| Lemma 2 (P1),(P2),(P3) hold after greedy Phase 1 | MRD : `phase1_inv`, `phase1_later` (executable Phase 1) | exhaustive sweeps (`verify_simple.py`) |
| Lemma 3 (the sink is a source) | MRD : `lastAgent_source`, `lastAgent_source_gen`; unassigned case `PAssign.unassigned_isSource` | sweep assertion "last agent always a source" |
| Lemma 4 (thin dump) | MRD : `PAssign.thin_dump`, `PAssign.dump_bound` | thin-dump assertion in `verify_user_p4_more.py` |
| Theorem 1: output complete and EFX₀ | MRD : `mrdG_efx0` (spec), `mrdGA_efx0` (array-backed executable), `mrdGA_eq` | ~70M Python runs; ~1M native runs; differential test |
| Theorem 1: all bundles but one of size ≤ 1 | MRD : `mrdG_shape` | — |
| Existence under |R_i| ≤ 2 | MRD : `twoRelevant_of_count`, `exists_efx0_of_count`, `main_theorem` | — |
| "Ties broken arbitrarily" | MRD : `efx0_of_invariants` (any assignment with (P1)–(P3)) | random tie-breaking sweeps |
| Remark: rotation loop never fires; earlier algorithm sound and live | MRD : `findCycle_phase1`, `phase2_phase1`, `mrd_sound`, `mrd_correct` | "cycles after Phase 1 = 0" in sweeps |
| Checker used on concrete instances is trustworthy | MRD : `efx0Check_iff` (sound and complete); MRDMono : `MInst.efx0Check_sound` | mutation tests (`verify_mutation.py`) |
| Beyond additivity (general monotone on two goods) | MRDMono : `PA.dump_efx0`, `mrdM_efx0`, `mrdM_shape`, `main_theorem`, example `exM_ok` | exhaustive monotone sweeps (`verify_monotone_simple.py`) |
| Additive theorem is a corollary of the monotone one | MRDBridge : `bundleVal_eq`, `efx0_iff`, `additive_via_monotone` | — |
| Degree-3 sharpness example (exactly two EFX₀ allocations) | MRDDeg3 : `sharp` (kernel-checked over all 16 allocations via the complete checker) | exhaustive check (`verify_p4.py`) |
| Running time O(n+m) | not formalized (the Lean executables use quadratic search helpers; the bound is about the algorithm with array bookkeeping) | — |
| Values are natural numbers in Lean; reals by the same argument | stated as a caveat, not formalized | — |
