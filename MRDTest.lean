import MRD
open MRD

/-!
# Native random-test driver

Runs the verified array-backed executables on pseudo-random 2-relevant additive instances and
checks every output with the Boolean checker `efx0Check`: `mrdLA` (the paper's Algorithm 1, equal
to its specification `mrdL` by `mrdLA_eq`), `mrdGA` (the variant preferring an unassigned sink) and
`mrdA` (the superseded rotation variant). For `mrdLA` the shape property (all bundles but one of
size at most one) is checked as well. The process exits with status 1 if any check fails.

The specification-level definitions (`mrdL`, `mrdG`, `mrd` and the monotone `MRDM.mrdML`) are not
run here: the compiler eta-expands them and recomputes Phase 1 on every lookup, which is
prohibitively slow. `mrdML` has no array-backed form; it is exercised by the kernel-checked example
`MRDM.exM_ok`.

Usage: `lake exe mrdtest [trials] [max agents] [max goods] [seed]`.
-/

/-- A linear congruential generator. -/
def lcg (x : Nat) : Nat := (1103515245 * x + 12345) % 2147483648

/-- Instance from a seed: each agent gets 0, 1 or 2 relevant goods with values 1..5. -/
def mkInst (seed n m : Nat) : Inst where
  n := n
  m := m
  v := fun i g =>
    let h1 := lcg (seed + 7919 * i.val + 1)
    let h2 := lcg h1
    let h3 := lcg h2
    let g1 := h1 % m
    let g2 := h2 % m
    let kind := h3 % 10
    if kind = 0 then 0
    else if g.val = g1 then 1 + (lcg (h3 + 1)) % 5
    else if kind ≥ 3 ∧ g.val = g2 then 1 + (lcg (h3 + 2)) % 5
    else 0

/-- Tabulate an allocation into an array, so that the checkers use constant-time lookups. -/
def tabulate {n m : Nat} (X : Fin m → Fin n) : Fin m → Fin n :=
  lookup (Array.ofFn X) Array.size_ofFn
where
  lookup (arr : Array (Fin n)) (h : arr.size = m) : Fin m → Fin n :=
    fun g => arr[g.val]'(by rw [h]; exact g.isLt)

/-- `true` iff all bundles but at most one have size at most one. -/
def thinShape (n m : Nat) (X : Fin m → Fin n) : Bool :=
  decide (finSum n (fun j => if 2 ≤ finSum m (fun g => if X g = j then 1 else 0) then 1 else 0) ≤ 1)

/-- Entry point: runs the executables on random instances, reports per-algorithm failure counts, and
exits with status 1 if any check failed. -/
def main (args : List String) : IO Unit := do
  let trials := (args.head?.bind String.toNat?).getD 1000
  let nmax := ((args.drop 1).head?.bind String.toNat?).getD 7
  let mmax := ((args.drop 2).head?.bind String.toNat?).getD 8
  let seed := ((args.drop 3).head?.bind String.toNat?).getD 2026
  IO.println s!"mrdtest: trials={trials} max-agents={nmax} max-goods={mmax} seed={seed}"
  let mut failL := 0
  let mut failG := 0
  let mut failA := 0
  let mut s := seed
  for _ in [0:trials] do
    s := lcg s
    let n := 1 + s % nmax
    let m := 1 + (lcg s) % mmax
    let I := mkInst (lcg (lcg s)) n m
    let hn : 0 < I.n := by show 0 < 1 + s % nmax; omega
    match mrdLA I hn with
    | some X0 =>
      let X := tabulate X0
      if !(I.efx0Check X) || !(thinShape I.n I.m X) then failL := failL + 1
    | none => failL := failL + 1
    match mrdGA I hn with
    | some Y => if !(I.efx0Check Y) then failG := failG + 1
    | none => failG := failG + 1
    match mrdA I with
    | some X => if !(I.efx0Check X) then failA := failA + 1
    | none => failA := failA + 1
  let failures := failL + failG + failA
  IO.println s!"trials={trials} failures={failures} (mrdLA={failL} mrdGA={failG} mrdA={failA})"
  if failures > 0 then IO.Process.exit 1
