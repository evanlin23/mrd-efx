import MRD
open MRD

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

def checkOne (I : Inst) : Bool :=
  match mrdA I with
  | some X => I.efx0Check X
  | none => false

def main (args : List String) : IO Unit := do
  let trials := (args.head?.bind String.toNat?).getD 1000
  let nmax := ((args.drop 1).head?.bind String.toNat?).getD 7
  let mmax := ((args.drop 2).head?.bind String.toNat?).getD 8
  let seed := ((args.drop 3).head?.bind String.toNat?).getD 2026
  let mut failures := 0
  let mut s := seed
  let mut noneCount := 0
  for _ in [0:trials] do
    s := lcg s
    let n := 1 + s % nmax
    let m := 1 + (lcg s) % mmax
    let I := mkInst (lcg (lcg s)) n m
    match mrdA I with
    | none => noneCount := noneCount + 1; failures := failures + 1
    | some X => if !(I.efx0Check X) then failures := failures + 1
    let hn : 0 < I.n := by show 0 < 1 + s % nmax; omega
    match mrdGA I hn with
    | some Y => if !(I.efx0Check Y) then failures := failures + 1000
    | none => failures := failures + 1000
  IO.println s!"trials={trials} failures={failures} (rotation variant no-output={noneCount}; simplified-algorithm failures counted x1000)"
