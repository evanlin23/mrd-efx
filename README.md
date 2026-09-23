# Strong EFX₀ for 2-relevant agents — Lean 4 formalization

[![verify](https://github.com/evanlin23/mrd-efx/actions/workflows/lean.yml/badge.svg)](https://github.com/evanlin23/mrd-efx/actions/workflows/lean.yml)

Formal companion to the paper *Strong EFX Allocations Exist When Every Agent Values at Most Two
Goods* (Evan Lin and Gerald Osterhaus, 2026). Every theorem of the paper is proved in core Lean 4
(no Mathlib), including the executable algorithms; the section "Not formalized" below lists what
is deliberately outside the development.

Toolchain: **leanprover/lean4:v4.34.0**, pinned in `lean-toolchain`; `elan` installs it on first
use. The release corresponding to the paper is tag `v1.2.0` (see `CHANGELOG.md`).

## Build and audit

    # install elan once: https://github.com/leanprover/elan
    ./check.sh

The script fails if any source file contains the word `sorry`, if the build reports an error or a
warning, if any `#print axioms` certificate lists an axiom other than `propext`,
`Classical.choice` and `Quot.sound`, or if the number of certificates differs from the number of
`#print axioms` commands in the sources. On success the last line is

    CHECK PASSED: 54 audited statements, 155 theorems, standard axioms only

where the first number counts the certificates (one for every theorem named in the paper's
appendix plus the headline results of each module) and the second the `theorem` declarations in
the sources, all of which the kernel checked. The reproducible `./check.sh` run, and the CI run on
every push (`.github/workflows/lean.yml`), are the certificate; `BUILDLOG-lean-4.34.0.txt` is a
convenience copy of the build output from a fresh checkout.

To check one theorem interactively, put `import MRD` and `#print axioms MRD.main_theorem_L` in a
scratch file and run `lake env lean scratch.lean` after `lake build`.

## Native random test

    lake build mrdtest
    lake exe mrdtest 20000 12 14 7   # trials, max agents, max goods, seed (the CI parameters)

The driver generates pseudo-random 2-relevant additive instances with values in 1..5, runs the
array-backed executables `mrdLA` (the paper's Algorithm 1; equal to its specification `mrdL` by
`mrdLA_eq`), `mrdGA` and `mrdA`, checks every output with the Boolean EFX₀ checker and, for
`mrdLA`, the shape property, and exits with status 1 on any failure. The specification-level
definitions are not run: the compiler recomputes Phase 1 on every lookup of their output, which is
prohibitively slow. The monotone algorithm `mrdML` has no array-backed form and is exercised by the
kernel-checked example `MRDM.exM_ok`. CI runs the driver after the audit; `check.sh` does not. Use
`lake exe`: the interpreter (`lean --run`) is orders of magnitude slower.

## Glossary

* **dump**: the paper's sink step; every unassigned good goes to the sink.
* Suffix **`L`** (`mrdL`, `mrdML`, `main_theorem_L`): the sink is the agent processed last (the
  paper's algorithms).
* **`mrdG`**, **`mrdM`**: the variant that prefers an unassigned agent as the sink and falls back to
  the last agent.
* Suffix **`A`** (`mrdA`, `mrdGA`): array-backed executable proved equal to its specification.
* **`mrd`**, **`mrdA`**: the superseded variant with a cycle-rotation phase; **MRD** abbreviates
  match–rotate–dump, its original name. The paper's algorithm is the match–dump special case: after
  the greedy phase the envy digraph has no cycle (`findCycle_phase1`), so the rotation phase is
  the identity.
* **`MRDM`**: the namespace of module `MRDMono` (monotone valuations).

## Trusted base

The definitions a reader must accept to believe the theorems, quoted from the sources.

Additive model (`MRD.lean`):

    structure Inst where
      n : Nat
      m : Nat
      v : Fin n → Fin m → Nat

    /-- 2-relevance, stated without counting: no agent has three distinct positively valued goods. -/
    def TwoRelevant : Prop :=
      ∀ i (g1 g2 g3 : Fin I.m), g1 ≠ g2 → g1 ≠ g3 → g2 ≠ g3 →
        0 < I.v i g1 → 0 < I.v i g2 → 0 < I.v i g3 → False

    /-- A complete allocation is an owner map. -/
    abbrev Alloc := Fin I.m → Fin I.n

    /-- Value, for agent `i`, of agent `j`'s bundle with the good `ex` (if any) removed. -/
    def bundleVal (X : I.Alloc) (i j : Fin I.n) (ex : Option (Fin I.m)) : Nat :=
      finSum I.m (fun g => if X g = j ∧ ex ≠ some g then I.v i g else 0)

    /-- Strong EFX₀: for all `i ≠ j` and every good `g ∈ X_j`, `v_i(X_i) ≥ v_i(X_j \ {g})`. -/
    def EFX0 (X : I.Alloc) : Prop :=
      ∀ i j : Fin I.n, i ≠ j → ∀ g : Fin I.m, X g = j →
        I.bundleVal X i j (some g) ≤ I.bundleVal X i i none

`finSum k f` is the sum of `f` over `Fin k`, and `numRelevant I i` counts the goods with
`0 < I.v i g`. The headline statement:

    theorem main_theorem_L (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 2) :
        ∃ X : I.Alloc, I.EFX0 X ∧ ∃ s, ∀ j, j ≠ s → ∀ g g', X g = j → X g' = j → g = g'

Monotone model (`MRDMono.lean`): an agent has slots `a i`, `b i` (equal for a one-good agent) and a
value table `f i` indexed by slot membership, normalised and monotone.

    structure MInst where
      n : Nat
      m : Nat
      a : Fin n → Fin m
      b : Fin n → Fin m
      f : Fin n → Bool → Bool → Nat
      f00 : ∀ i, f i false false = 0
      mono_a : ∀ i, f i false true ≤ f i true true
      mono_b : ∀ i, f i true false ≤ f i true true

    def sv (i : Fin I.n) (g : Fin I.m) : Nat := I.f i (decide (g = I.a i)) (decide (g = I.b i))

    def bundleVal (X : I.Alloc) (i j : Fin I.n) (ex : Option (Fin I.m)) : Nat :=
      I.f i (I.has X j ex (I.a i)) (I.has X j ex (I.b i))

    def EFX0 (X : I.Alloc) : Prop :=
      ∀ i j : Fin I.n, i ≠ j → ∀ g : Fin I.m, X g = j →
        I.bundleVal X i j (some g) ≤ I.bundleVal X i i none

where `I.has X j ex g` is `decide (X g = j ∧ ex ≠ some g)`.

## Contents

* `MRD.lean` — additive model. Main theorems: `MRD.main_theorem_L` (existence + shape under
  |R_i| <= 2, via `MRD.mrdL_efx0`: greedy, then every unassigned good goes to the last agent, who is
  always a source by `MRD.lastAgent_source_all`), `MRD.main_theorem`/`MRD.mrdG_efx0` (the variant
  that prefers an unassigned agent as the sink), `MRD.efx0_of_invariants` (tie-breaking
  independence), `MRD.efx0Check_iff` (sound and complete checker), `MRD.mrdLA_eq`/`MRD.mrdA_eq`/`MRD.mrdGA_eq`
  (array-backed executables equal the specifications), and `MRD.mrd_correct` (the superseded
  rotation variant: sound and live; not part of the paper).
* `MRDMono.lean` — general monotone valuations on at most two goods (substitutes, complements, ...).
  Main theorems: `MRDM.mrdML_efx0`/`MRDM.main_theorem_L` (last agent is the sink) and
  `MRDM.mrdM_efx0`/`MRDM.main_theorem` (unassigned agent preferred). Kernel-checked example
  `MRDM.exM_ok` with a complementary agent.
* `MRDBridge.lean` — embeds every 2-relevant additive instance with at least one good into the
  monotone model and proves the two `EFX0` predicates coincide (`MRDBridge.efx0_iff`); hence the
  additive theorem is a corollary of the monotone one (`MRDBridge.additive_via_monotone_L` for the
  paper's Algorithm 2, `MRDBridge.additive_via_monotone` for the variant).
* `MRDDeg3.lean` — the degree-3 sharpness example: exactly two of the sixteen allocations are
  strongly EFX₀ (`MRDDeg3.sharp`), kernel-checked through the complete checker; no EFX₀ allocation
  has all bundles but one of size ≤ 1 (`MRDDeg3.no_thin_shape`), and every EFX₀ allocation gives
  some agent two of its relevant goods (`MRDDeg3.two_relevant_goods`).
* `MRDTest.lean` — native driver running the verified executables on random instances.

## Correspondence with the paper

Every Lean name below has a `#print axioms` certificate in the build.

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
| Additive theorem as a corollary of the monotone one (m ≥ 1) | MRDBridge : `efx0_iff`, `additive_via_monotone_L` |
| Checker soundness and completeness | MRD : `efx0Check_iff` |
| Degree-3 sharpness example | MRDDeg3 : `sharp`, `no_thin_shape`, `two_relevant_goods` |

## Not formalized

* The running-time bound O(n+m): it concerns the algorithm with array bookkeeping, while the Lean
  executables use quadratic search helpers.
* Real-valued utilities: values are natural numbers in Lean; the argument only compares values, so
  it applies verbatim to nonnegative reals.
* The bridge theorems assume at least one good (`0 < I.m`); with no goods every statement is
  trivial. Only the EFX₀ conclusion transfers through the embedding; the executable-level identity
  `mrdL I = mrdML (toM I)` is not claimed.

## Citing and license

Apache-2.0 (see `LICENSE`). Citation metadata is in `CITATION.cff`; cite tag `v1.2.0`.
