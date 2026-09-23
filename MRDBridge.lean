import MRD
import MRDMono
set_option autoImplicit false

/-!
# Bridge: the additive theorem is a corollary of the general-monotone one

Given a 2-relevant additive instance `I` (no agent has three distinct positively valued goods) with
at least one good, we build the monotone instance `toM I` whose slots are the (at most two)
positively valued goods of each agent and whose table is the corresponding sum, prove that the two
bundle-value functions coincide on every bundle (`bundleVal_eq`), hence that the two `EFX0`
predicates coincide (`efx0_iff`), and conclude that the monotone algorithms produce strongly-EFX₀
allocations for `I` (`additive_via_monotone_L` for the paper's Algorithm 2, `additive_via_monotone`
for the variant preferring an unassigned sink). Only the EFX₀ conclusion transfers: the
executable-level identity `mrdL I = mrdML (toM I hm)` is not claimed.
-/

namespace MRDBridge
open MRD (finSum finSum_add finSum_eq_single findFin findFin_some findFin_none ifp ifn)

/-- A sum with support in two distinct indices. -/
theorem finSum_eq_two (k : Nat) (F : Fin k → Nat) (x y : Fin k) (hxy : x ≠ y)
    (hz : ∀ i, i ≠ x → i ≠ y → F i = 0) : finSum k F = F x + F y := by
  have hsplit : F = fun i => (if i = x then F x else 0) + (if i = y then F y else 0) := by
    funext i
    by_cases ex : i = x
    · rw [ex]; simp [hxy]
    · by_cases ey : i = y
      · rw [ey]; simp [Ne.symm hxy]
      · simp [ex, ey, hz i ex ey]
  have h1 : finSum k (fun i => (if i = x then F x else 0) + (if i = y then F y else 0))
      = finSum k (fun i => if i = x then F x else 0) +
        finSum k (fun i => if i = y then F y else 0) :=
    finSum_add k _ _
  rw [hsplit, h1, finSum_eq_single k _ x (fun i hi => by simp [hi]),
    finSum_eq_single k _ y (fun i hi => by simp [hi])]
  simp [hxy, Ne.symm hxy]

variable (I : MRD.Inst)

/-- First positively valued good of `i`, if any. -/
def firstPos (i : Fin I.n) : Option (Fin I.m) := findFin I.m (fun g => decide (0 < I.v i g))

/-- The first slot of `i`: its first positively valued good (or good `0` if it has none). -/
def slotA (hm : 0 < I.m) (i : Fin I.n) : Fin I.m := (firstPos I i).getD ⟨0, hm⟩

/-- The second slot of `i`: its next positively valued good, or `slotA` again if there is none. -/
def slotB (hm : 0 < I.m) (i : Fin I.n) : Fin I.m :=
  (findFin I.m (fun g => decide (0 < I.v i g ∧ g ≠ slotA I hm i))).getD (slotA I hm i)

/-- If `i` values some good positively, then it values `slotA` positively. -/
theorem slotA_pos (hm : 0 < I.m) (i : Fin I.n) (g : Fin I.m) (hg : 0 < I.v i g) :
    0 < I.v i (slotA I hm i) := by
  unfold slotA
  cases hf : firstPos I i with
  | none =>
    have := findFin_none _ _ hf g
    simp at this
    rw [this] at hg
    exact absurd hg (Nat.lt_irrefl 0)
  | some a0 =>
    have := findFin_some _ _ _ hf
    simpa using this

/-- Every positively valued good is one of the two slots. -/
theorem pos_slot (hI : I.TwoRelevant) (hm : 0 < I.m) (i : Fin I.n) (g : Fin I.m)
    (hg : 0 < I.v i g) :
    g = slotA I hm i ∨ g = slotB I hm i := by
  by_cases ha : g = slotA I hm i
  · exact Or.inl ha
  · right
    unfold slotB
    cases hf : findFin I.m (fun g => decide (0 < I.v i g ∧ g ≠ slotA I hm i)) with
    | none =>
      have := findFin_none _ _ hf g
      simp at this
      exact absurd (this hg) ha
    | some b0 =>
      show g = b0
      have hb := findFin_some _ _ _ hf
      simp at hb
      by_cases hgb : g = b0
      · exact hgb
      · exfalso
        exact hI i (slotA I hm i) b0 g (Ne.symm hb.2) (Ne.symm ha) (Ne.symm hgb)
          (slotA_pos I hm i g hg) hb.1 hg

/-- Goods that are neither slot are worthless to `i`. -/
theorem v_zero_off_slots (hI : I.TwoRelevant) (hm : 0 < I.m) (i : Fin I.n) (g : Fin I.m)
    (ha : g ≠ slotA I hm i) (hb : g ≠ slotB I hm i) : I.v i g = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  rcases pos_slot I hI hm i g hp with e | e
  · exact ha e
  · exact hb e

/-- The value table: the sum of the (at most two) slot values present. -/
def tbl (hm : 0 < I.m) (i : Fin I.n) (ha hb : Bool) : Nat :=
  (if ha then I.v i (slotA I hm i) else 0) +
  (if hb && decide (slotA I hm i ≠ slotB I hm i) then I.v i (slotB I hm i) else 0)

/-- The monotone instance associated with `I`. -/
def toM (hm : 0 < I.m) : MRDM.MInst where
  n := I.n
  m := I.m
  a := slotA I hm
  b := slotB I hm
  f := tbl I hm
  f00 := by intro i; simp [tbl]
  mono_a := by intro i; simp [tbl]
  mono_b := by intro i; simp [tbl]

/-- The two bundle-value functions agree on every bundle. -/
theorem bundleVal_eq (hI : I.TwoRelevant) (hm : 0 < I.m) (X : I.Alloc) (i j : Fin I.n)
    (ex : Option (Fin I.m)) : I.bundleVal X i j ex = (toM I hm).bundleVal X i j ex := by
  have hz : ∀ g, g ≠ slotA I hm i → g ≠ slotB I hm i →
      (if X g = j ∧ ex ≠ some g then I.v i g else 0) = 0 := by
    intro g ha hb
    simp [v_zero_off_slots I hI hm i g ha hb]
  show finSum I.m (fun g => if X g = j ∧ ex ≠ some g then I.v i g else 0)
    = tbl I hm i (decide (X (slotA I hm i) = j ∧ ex ≠ some (slotA I hm i)))
        (decide (X (slotB I hm i) = j ∧ ex ≠ some (slotB I hm i)))
  by_cases hab : slotA I hm i = slotB I hm i
  · rw [finSum_eq_single I.m _ (slotA I hm i) (fun g hg => hz g hg (by rw [← hab]; exact hg))]
    unfold tbl
    simp [hab]
  · rw [finSum_eq_two I.m _ (slotA I hm i) (slotB I hm i) hab hz]
    unfold tbl
    simp [hab]

/-- The two EFX₀ predicates coincide. -/
theorem efx0_iff (hI : I.TwoRelevant) (hm : 0 < I.m) (X : I.Alloc) :
    I.EFX0 X ↔ (toM I hm).EFX0 X := by
  constructor
  · intro h i j hij g hg
    have h' := h i j hij g hg
    rw [bundleVal_eq I hI hm X i j (some g), bundleVal_eq I hI hm X i i none] at h'
    exact h'
  · intro h i j hij g hg
    rw [bundleVal_eq I hI hm X i j (some g), bundleVal_eq I hI hm X i i none]
    exact h i j hij g hg

/-- **The additive theorem as a corollary of the monotone one**, for the variant preferring an
unassigned sink. -/
theorem additive_via_monotone (hI : I.TwoRelevant) (hn : 0 < I.n) (hm : 0 < I.m) :
    I.EFX0 (MRDM.mrdM (toM I hm) hn) :=
  (efx0_iff I hI hm _).mpr (MRDM.mrdM_efx0 (toM I hm) hn)

/-- **The additive theorem as a corollary of the monotone one**: the paper's Algorithm 2 on the
embedded instance is strongly EFX₀ for the additive instance (assuming at least one good). -/
theorem additive_via_monotone_L (hI : I.TwoRelevant) (hn : 0 < I.n) (hm : 0 < I.m) :
    I.EFX0 (MRDM.mrdML (toM I hm) hn) :=
  (efx0_iff I hI hm _).mpr (MRDM.mrdML_efx0 (toM I hm) hn)

end MRDBridge

#print axioms MRDBridge.bundleVal_eq
#print axioms MRDBridge.efx0_iff
#print axioms MRDBridge.additive_via_monotone
#print axioms MRDBridge.additive_via_monotone_L
