import MRD
set_option autoImplicit false

/-!
# The degree-3 sharpness example, kernel-checked

Two agents with identical additive values $3,2,2,0$ on goods $a,b,c,d$ (each agent has three
relevant goods, so this is outside the 2-relevant class). Exactly two of the sixteen allocations are
strongly EFX₀, namely $(\{a,d\},\{b,c\})$ and its mirror image, and in both an agent holds two
relevant goods — which is why the one-good-per-agent framework cannot extend to three relevant
goods.
-/

namespace MRDDeg3
open MRD (allFin allFin_true allFin_of_forall)

def I3 : MRD.Inst where
  n := 2
  m := 4
  v := fun _ g => match g.val with | 0 => 3 | 1 => 2 | 2 => 2 | _ => 0

abbrev Alloc4 := Fin 4 → Fin 2

/-- Decode an allocation from its 4-bit code. -/
def decode (k : Fin 16) : Alloc4
  | ⟨0, _⟩ => ⟨k.val % 2, Nat.mod_lt _ (by decide)⟩
  | ⟨1, _⟩ => ⟨(k.val / 2) % 2, Nat.mod_lt _ (by decide)⟩
  | ⟨2, _⟩ => ⟨(k.val / 4) % 2, Nat.mod_lt _ (by decide)⟩
  | ⟨_, _⟩ => ⟨(k.val / 8) % 2, Nat.mod_lt _ (by decide)⟩

def encode (X : Alloc4) : Fin 16 :=
  ⟨(X ⟨0, by decide⟩).val + 2 * (X ⟨1, by decide⟩).val + 4 * (X ⟨2, by decide⟩).val +
      8 * (X ⟨3, by decide⟩).val,
   by
     have h0 := (X ⟨0, by decide⟩).isLt
     have h1 := (X ⟨1, by decide⟩).isLt
     have h2 := (X ⟨2, by decide⟩).isLt
     have h3 := (X ⟨3, by decide⟩).isLt
     omega⟩

/-- Every allocation is the decoding of its code. -/
theorem decode_encode (X : Alloc4) : decode (encode X) = X := by
  funext g
  have h0 := (X ⟨0, by decide⟩).isLt
  have h1 := (X ⟨1, by decide⟩).isLt
  have h2 := (X ⟨2, by decide⟩).isLt
  have h3 := (X ⟨3, by decide⟩).isLt
  apply Fin.ext
  match g with
  | ⟨0, h⟩ =>
    show (decode (encode X) ⟨0, by decide⟩).val = (X ⟨0, by decide⟩).val
    simp only [decode, encode]
    omega
  | ⟨1, h⟩ =>
    show (decode (encode X) ⟨1, by decide⟩).val = (X ⟨1, by decide⟩).val
    simp only [decode, encode]
    omega
  | ⟨2, h⟩ =>
    show (decode (encode X) ⟨2, by decide⟩).val = (X ⟨2, by decide⟩).val
    simp only [decode, encode]
    omega
  | ⟨3, h⟩ =>
    show (decode (encode X) ⟨3, by decide⟩).val = (X ⟨3, by decide⟩).val
    simp only [decode, encode]
    omega

/-- Pointwise Boolean equality of allocations, with its characterisation. -/
def eqB (X Y : Alloc4) : Bool := allFin 4 (fun g => decide (X g = Y g))

theorem eqB_iff (X Y : Alloc4) : eqB X Y = true ↔ X = Y := by
  constructor
  · intro h
    funext g
    exact of_decide_eq_true (allFin_true _ _ h g)
  · intro h
    subst h
    exact allFin_of_forall _ _ (fun g => decide_eq_true rfl)

/-- $(\{a,d\},\{b,c\})$: goods $0,3$ to agent $0$, goods $1,2$ to agent $1$ — code $6$. -/
def X1 : Alloc4 := decode ⟨6, by decide⟩
/-- Its mirror image — code $9$. -/
def X2 : Alloc4 := decode ⟨9, by decide⟩

/-- **Sharpness, kernel-checked**: an allocation is strongly EFX₀ iff it is one of the two above. -/
theorem sharp (X : Alloc4) : I3.EFX0 X ↔ (X = X1 ∨ X = X2) := by
  have hall : allFin 16 (fun k => decide ((I3.efx0Check (decode k) = true) ↔
      (eqB (decode k) X1 = true ∨ eqB (decode k) X2 = true))) = true := by decide
  have hk := of_decide_eq_true (allFin_true _ _ hall (encode X))
  rw [decode_encode, MRD.efx0Check_iff I3 X, eqB_iff, eqB_iff] at hk
  exact hk

/-- No EFX₀ allocation of this instance has the shape produced by the 2-relevant algorithm
(all bundles but one of size at most one): in both EFX₀ allocations two bundles have size two. -/
theorem no_thin_shape (X : Alloc4) (hX : I3.EFX0 X) :
    ¬ ∃ s : Fin 2, ∀ j, j ≠ s → ∀ g g', X g = j → X g' = j → g = g' := by
  rintro ⟨s, hs⟩
  rcases (sharp X).1 hX with rfl | rfl
  · -- `X1`: goods 0,3 to agent 0 and goods 1,2 to agent 1
    rcases s with ⟨_ | _ | n, hn⟩
    · exact absurd
        (hs ⟨1, by decide⟩ (by intro h; cases h) ⟨1, by decide⟩ ⟨2, by decide⟩
          (by decide) (by decide))
        (by decide)
    · exact absurd
        (hs ⟨0, by decide⟩ (by intro h; cases h) ⟨0, by decide⟩ ⟨3, by decide⟩
          (by decide) (by decide))
        (by decide)
    · omega
  · -- `X2`: goods 1,2 to agent 0 and goods 0,3 to agent 1
    rcases s with ⟨_ | _ | n, hn⟩
    · exact absurd
        (hs ⟨1, by decide⟩ (by intro h; cases h) ⟨0, by decide⟩ ⟨3, by decide⟩
          (by decide) (by decide))
        (by decide)
    · exact absurd
        (hs ⟨0, by decide⟩ (by intro h; cases h) ⟨1, by decide⟩ ⟨2, by decide⟩
          (by decide) (by decide))
        (by decide)
    · omega

/-- In every EFX₀ allocation of this instance some agent holds two of its relevant goods. -/
theorem two_relevant_goods (X : Alloc4) (hX : I3.EFX0 X) :
    ∃ i : Fin 2, ∃ g g' : Fin 4, g ≠ g' ∧ X g = i ∧ X g' = i ∧ 0 < I3.v i g ∧ 0 < I3.v i g' := by
  rcases (sharp X).1 hX with rfl | rfl
  · exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩,
      by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩,
      by decide, by decide, by decide, by decide, by decide⟩

end MRDDeg3

#print axioms MRDDeg3.decode_encode
#print axioms MRDDeg3.sharp
#print axioms MRDDeg3.no_thin_shape
#print axioms MRDDeg3.two_relevant_goods
