/-!
# Match–Dump for 2-relevant additive instances: a complete formal verification

Core Lean 4 only (no Mathlib). Model: `n` agents, `m` goods, additive values `v i g : Nat`; a good is
relevant to `i` iff `0 < v i g`; the instance is 2-relevant iff no agent has three distinct relevant
goods (`twoRelevant_of_count` shows the counting form `|R_i| ≤ 2` implies this). Fairness: strong
`EFX₀` (the removed good may be worthless to the envier).

There is no `sorry` in this file. Main results (see `#print axioms` at the end):
* `dump_efx0` – the dump step is EFX₀ for every assignment satisfying (P1),(P2) and every source;
* `phase1_inv`, `phase1_later`, `phase1_holders` – the executable greedy Phase 1 satisfies the invariants;
* `mrdG_efx0`, `mrdG_shape`, `exists_efx0_of_count` – the simplified algorithm (greedy, then dump on an
  unassigned agent or else the last agent) always outputs a complete EFX₀ allocation with all bundles
  but one of size ≤ 1; existence under the hypothesis `|R_i| ≤ 2`;
* `mrd_sound`, `mrd_total_unconditional`, `mrd_correct` – the rotation-based variant is sound and
  live: after a greedy Phase 1 the envy digraph has no cycle (`findCycle_phase1`), so Phase 2 is the
  identity (`phase2_phase1`);
* `efx0Check_iff` – the Boolean EFX₀ checker is sound and complete;
* `mrdA_eq`, `mrdGA_eq` – array-backed executables equal the specifications.
-/

set_option autoImplicit false

namespace MRD

/-- Version-independent replacements for `if_pos` / `if_neg` (deprecated in newer Lean releases). -/
theorem ifp {c : Prop} [Decidable c] {α : Sort _} (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]
theorem ifn {c : Prop} [Decidable c] {α : Sort _} (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

/-! ## Sums and searches over `Fin` -/

/-- Sum of `f` over `Fin k`. -/
def finSum : (k : Nat) → (Fin k → Nat) → Nat
  | 0, _ => 0
  | k+1, f => finSum k (fun i => f i.castSucc) + f (Fin.last k)

/-- Every element of `Fin (k+1)` is a `castSucc` or the last element. -/
theorem fin_cases (k : Nat) (i : Fin (k+1)) : (∃ j : Fin k, i = j.castSucc) ∨ i = Fin.last k := by
  by_cases h : i.val < k
  · exact Or.inl ⟨⟨i.val, h⟩, Fin.ext (by simp)⟩
  · have := i.isLt
    exact Or.inr (Fin.ext (by simp [Fin.val_last]; omega))

theorem finSum_zero (k : Nat) (f : Fin k → Nat) (h : ∀ i, f i = 0) : finSum k f = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc) (fun i => h _), h]

theorem finSum_eq_single (k : Nat) (f : Fin k → Nat) (h : Fin k) (hz : ∀ i, i ≠ h → f i = 0) :
    finSum k f = f h := by
  induction k with
  | zero => exact Fin.elim0 h
  | succ k ih =>
    simp only [finSum]
    rcases fin_cases k h with ⟨h', rfl⟩ | rfl
    · have hl : f (Fin.last k) = 0 := by
        apply hz
        intro e
        have e' := congrArg Fin.val e
        have := h'.isLt
        simp at e'
        omega
      rw [hl, Nat.add_zero]
      apply ih (fun i => f i.castSucc) h'
      intro i hi
      apply hz
      intro e
      exact hi (Fin.ext (by have := congrArg Fin.val e; simpa using this))
    · have : finSum k (fun i => f i.castSucc) = 0 := by
        apply finSum_zero
        intro i
        apply hz
        intro e
        have e' := congrArg Fin.val e
        have := i.isLt
        simp at e'
        omega
      rw [this, Nat.zero_add]

/-- The first index satisfying `p`, if any. -/
def findFin : (k : Nat) → (Fin k → Bool) → Option (Fin k)
  | 0, _ => none
  | k+1, p =>
    match findFin k (fun i => p i.castSucc) with
    | some i => some i.castSucc
    | none => if p (Fin.last k) then some (Fin.last k) else none

theorem findFin_some (k : Nat) (p : Fin k → Bool) (i : Fin k) (h : findFin k p = some i) :
    p i = true := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    simp only [findFin] at h
    split at h
    · rename_i i' hi'
      cases h
      exact ih _ i' hi'
    · split at h
      · cases h
        assumption
      · cases h

theorem findFin_none (k : Nat) (p : Fin k → Bool) (h : findFin k p = none) : ∀ i, p i = false := by
  induction k with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
    intro i
    simp only [findFin] at h
    split at h
    · cases h
    · rename_i hnone
      split at h
      · cases h
      · rename_i hlast
        rcases fin_cases k i with ⟨i', rfl⟩ | rfl
        · exact ih _ hnone i'
        · exact Bool.eq_false_iff.mpr hlast

/-- `true` iff `p` holds on all of `Fin k`. -/
def allFin (k : Nat) (p : Fin k → Bool) : Bool := (findFin k (fun i => !p i)).isNone

theorem allFin_true (k : Nat) (p : Fin k → Bool) (h : allFin k p = true) : ∀ i, p i = true := by
  intro i
  unfold allFin at h
  cases hf : findFin k (fun i => !p i) with
  | some j => rw [hf] at h; simp at h
  | none =>
    have := findFin_none k _ hf i
    simpa using this

/-! ## The model -/

/-- An additive fair-division instance. -/
structure Inst where
  n : Nat
  m : Nat
  v : Fin n → Fin m → Nat

namespace Inst
variable (I : Inst)

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

/-- Boolean checker for `EFX0`. -/
def efx0Check (X : I.Alloc) : Bool :=
  allFin I.n fun i => allFin I.n fun j =>
    if i = j then true else
    allFin I.m fun g =>
      if X g = j then decide (I.bundleVal X i j (some g) ≤ I.bundleVal X i i none) else true

/-- The checker is sound. -/
theorem efx0Check_sound (X : I.Alloc) (h : I.efx0Check X = true) : I.EFX0 X := by
  intro i j hij g hg
  have h1 := allFin_true _ _ h i
  have h2 := allFin_true _ _ h1 j
  rw [ifn hij] at h2
  have h3 := allFin_true _ _ h2 g
  rw [ifp hg] at h3
  exact of_decide_eq_true h3

end Inst

/-! ## Partial assignments, the digraph `D`, and the dump -/

/-- A partial injective assignment of relevant goods to agents. -/
structure PAssign (I : Inst) where
  ρ : Fin I.n → Option (Fin I.m)
  rel : ∀ i g, ρ i = some g → 0 < I.v i g
  inj : ∀ i j g, ρ i = some g → ρ j = some g → i = j

namespace PAssign
variable {I : Inst} (A : PAssign I)

/-- `u_i`: value of the held good, `0` if unassigned. -/
def util (i : Fin I.n) : Nat :=
  match A.ρ i with
  | some g => I.v i g
  | none => 0

theorem util_of_some (i : Fin I.n) (g : Fin I.m) (h : A.ρ i = some g) : A.util i = I.v i g := by
  simp [util, h]

theorem util_of_none (i : Fin I.n) (h : A.ρ i = none) : A.util i = 0 := by
  simp [util, h]

/-- The holder of a good, if any. -/
def holder (g : Fin I.m) : Option (Fin I.n) := findFin I.n (fun i => decide (A.ρ i = some g))

/-- A good is unassigned iff nobody holds it. -/
def Unassigned (g : Fin I.m) : Prop := ∀ i, A.ρ i ≠ some g

theorem holder_some (g : Fin I.m) (j : Fin I.n) (h : A.holder g = some j) : A.ρ j = some g := by
  have := findFin_some _ _ _ h
  simpa using this

theorem holder_none (g : Fin I.m) (h : A.holder g = none) : A.Unassigned g := by
  intro i hi
  have := findFin_none _ _ h i
  simp at this
  exact this hi

/-- Arc `i → j` of the full-agent digraph `D`: `j` holds a good that `i` values above `u_i`.
(Such a good is automatically relevant to `i`.) -/
def Arc (i j : Fin I.n) : Prop := ∃ g, A.ρ j = some g ∧ A.util i < I.v i g

/-- A source of `D`: in-degree zero. -/
def IsSource (s : Fin I.n) : Prop := ∀ i, ¬ A.Arc i s

/-- Invariant (P1): every relevant good of an unassigned agent is held by somebody. -/
def P1 : Prop := ∀ i, A.ρ i = none → ∀ g, 0 < I.v i g → ∃ j, A.ρ j = some g

/-- Invariant (P2): an assigned agent values its good at least as much as any unassigned good. -/
def P2 : Prop := ∀ i g, A.ρ i = some g → ∀ g', A.Unassigned g' → I.v i g' ≤ I.v i g

/-- Phase 4: every unassigned good goes to the sink `s`; assigned goods stay with their holder. -/
def dump (s : Fin I.n) : I.Alloc := fun g =>
  match A.holder g with
  | some j => j
  | none => s

/-- **Unassigned agents have in-degree zero**: every arc targets an assigned agent. -/
theorem unassigned_isSource (s : Fin I.n) (h : A.ρ s = none) : A.IsSource s := by
  intro i harc
  obtain ⟨g, hg, _⟩ := harc
  rw [h] at hg
  cases hg

/-- **An assigned source holds a secure good**: `v_i(ρ(s)) ≤ u_i` for every agent `i`. -/
theorem source_secure (s : Fin I.n) (g : Fin I.m) (hs : A.ρ s = some g) (hsrc : A.IsSource s) :
    ∀ i, I.v i g ≤ A.util i := by
  intro i
  apply Nat.le_of_not_lt
  intro hlt
  exact hsrc i ⟨g, hs, hlt⟩

/-- Consequence of (P1): an unassigned agent has no relevant unassigned good. -/
theorem unassigned_no_relevant_in_Z (hP1 : A.P1) (i : Fin I.n) (hi : A.ρ i = none)
    (g : Fin I.m) (hg : A.Unassigned g) : I.v i g = 0 := by
  cases Nat.eq_zero_or_pos (I.v i g) with
  | inl h0 => exact h0
  | inr hpos =>
    obtain ⟨j, hj⟩ := hP1 i hi g hpos
    exact absurd hj (hg j)

/-- Consequence of (P2): an assigned agent's utility dominates every unassigned good. -/
theorem assigned_Z_bounded (hP2 : A.P2) (i : Fin I.n) (g : Fin I.m) (hi : A.ρ i = some g)
    (g' : Fin I.m) (hg' : A.Unassigned g') : I.v i g' ≤ A.util i := by
  rw [A.util_of_some i g hi]
  exact hP2 i g hi g' hg'

/-- Who owns a good under the dump. -/
theorem dump_eq_iff (s j : Fin I.n) (hjs : j ≠ s) (g : Fin I.m) :
    A.dump s g = j ↔ A.ρ j = some g := by
  unfold dump
  cases hh : A.holder g with
  | some j' =>
    show j' = j ↔ _
    constructor
    · intro e; rw [← e]; exact A.holder_some g _ hh
    · intro hj
      have hj' := A.holder_some g j' hh
      exact A.inj j' j g hj' hj
  | none =>
    show s = j ↔ _
    constructor
    · intro e; exact absurd e.symm hjs
    · intro hj; exact absurd hj (A.holder_none g hh j)

theorem dump_self_iff (s : Fin I.n) (g : Fin I.m) :
    A.dump s g = s ↔ (A.ρ s = some g ∨ A.Unassigned g) := by
  unfold dump
  cases hh : A.holder g with
  | some j' =>
    show j' = s ↔ _
    constructor
    · intro e; rw [← e]; exact Or.inl (A.holder_some g _ hh)
    · intro h
      rcases h with hs | hun
      · exact A.inj j' _ g (A.holder_some g j' hh) hs
      · exact absurd (A.holder_some g j' hh) (hun j')
  | none =>
    show s = s ↔ _
    constructor
    · intro _; exact Or.inr (A.holder_none g hh)
    · intro _; rfl

/-- **Thin dump**: another agent has at most one relevant good in the sink's bundle.
Only (P1), injectivity and 2-relevance are needed. -/
theorem thin_dump (hI : I.TwoRelevant) (hP1 : A.P1) (s i : Fin I.n) (his : i ≠ s)
    (g1 g2 : Fin I.m) (h1 : A.dump s g1 = s) (h2 : A.dump s g2 = s)
    (r1 : 0 < I.v i g1) (r2 : 0 < I.v i g2) : g1 = g2 := by
  apply Decidable.byContradiction
  intro hne
  have c1 := (A.dump_self_iff s g1).mp h1
  have c2 := (A.dump_self_iff s g2).mp h2
  cases hi : A.ρ i with
  | none =>
    -- an unassigned agent has no relevant unassigned good, so both goods are held by `s`
    have e1 : A.ρ s = some g1 := by
      rcases c1 with hs | hun
      · exact hs
      · exact absurd r1 (by rw [A.unassigned_no_relevant_in_Z hP1 i hi g1 hun]; exact Nat.lt_irrefl 0)
    have e2 : A.ρ s = some g2 := by
      rcases c2 with hs | hun
      · exact hs
      · exact absurd r2 (by rw [A.unassigned_no_relevant_in_Z hP1 i hi g2 hun]; exact Nat.lt_irrefl 0)
    rw [e1] at e2
    exact hne (Option.some.inj e2)
  | some h =>
    -- `h`, `g1`, `g2` would be three distinct relevant goods of `i`
    have rh : 0 < I.v i h := A.rel i h hi
    have hh1 : h ≠ g1 := by
      intro e; subst e
      rcases c1 with hs | hun
      · exact his (A.inj i s h hi hs)
      · exact hun i hi
    have hh2 : h ≠ g2 := by
      intro e; subst e
      rcases c2 with hs | hun
      · exact his (A.inj i s h hi hs)
      · exact hun i hi
    exact hI i h g1 g2 hh1 hh2 hne rh r1 r2

/-- **Dump bound**: another agent does not prefer any good of the sink's bundle to its own good. -/
theorem dump_bound (hP1 : A.P1) (hP2 : A.P2) (s : Fin I.n) (hsrc : A.IsSource s)
    (i : Fin I.n) (g : Fin I.m) (hg : A.dump s g = s) : I.v i g ≤ A.util i := by
  rcases (A.dump_self_iff s g).mp hg with hs | hun
  · exact A.source_secure s g hs hsrc i
  · cases hi : A.ρ i with
    | none =>
      rw [A.unassigned_no_relevant_in_Z hP1 i hi g hun]
      exact Nat.zero_le _
    | some h => exact A.assigned_Z_bounded hP2 i h hi g hun

/-- The value of one's own bundle under the dump, for agents other than the sink. -/
theorem own_val (s i : Fin I.n) (his : i ≠ s) : I.bundleVal (A.dump s) i i none = A.util i := by
  unfold Inst.bundleVal
  cases hi : A.ρ i with
  | none =>
    rw [A.util_of_none i hi]
    apply finSum_zero
    intro g
    have : ¬ A.dump s g = i := by
      intro e
      have := (A.dump_eq_iff s i his g).mp e
      rw [hi] at this
      cases this
    simp [this]
  | some h =>
    rw [A.util_of_some i h hi]
    rw [finSum_eq_single I.m _ h]
    · have : A.dump s h = i := (A.dump_eq_iff s i his h).mpr hi
      simp [this]
    · intro g hg
      have : ¬ A.dump s g = i := by
        intro e
        have := (A.dump_eq_iff s i his g).mp e
        rw [hi] at this
        exact hg (Option.some.inj this).symm
      simp [this]

/-- Removing a good from a singleton bundle leaves nothing: bundles of agents other than the sink. -/
theorem other_val (s i j : Fin I.n) (hjs : j ≠ s) (g : Fin I.m) (hg : A.dump s g = j) :
    I.bundleVal (A.dump s) i j (some g) = 0 := by
  unfold Inst.bundleVal
  apply finSum_zero
  intro g'
  by_cases e : A.dump s g' = j
  · have e1 := (A.dump_eq_iff s j hjs g').mp e
    have e2 := (A.dump_eq_iff s j hjs g).mp hg
    rw [e1] at e2
    have : g' = g := Option.some.inj e2
    simp [this]
  · simp [e]

/-- The sink's bundle, minus any good, is worth at most `u_i` to any other agent. -/
theorem sink_val_le (hI : I.TwoRelevant) (hP1 : A.P1) (hP2 : A.P2) (s : Fin I.n)
    (hsrc : A.IsSource s) (i : Fin I.n) (his : i ≠ s) (g : Fin I.m) :
    I.bundleVal (A.dump s) i s (some g) ≤ A.util i := by
  unfold Inst.bundleVal
  -- the terms that can be nonzero are relevant goods of `i` in `X_s` other than `g`
  by_cases hex : ∃ g0, A.dump s g0 = s ∧ 0 < I.v i g0 ∧ g0 ≠ g
  · obtain ⟨g0, hg0, r0, hne⟩ := hex
    rw [finSum_eq_single I.m _ g0]
    · have hne' : some g ≠ some g0 := by intro e; exact hne (Option.some.inj e).symm
      rw [ifp (And.intro hg0 hne')]
      exact A.dump_bound hP1 hP2 s hsrc i g0 hg0
    · intro g' hg'
      by_cases c : A.dump s g' = s ∧ some g ≠ some g'
      · cases Nat.eq_zero_or_pos (I.v i g') with
        | inl h0 => simp [h0]
        | inr hpos =>
          have : g' = g0 := A.thin_dump hI hP1 s i his g' g0 c.1 hg0 hpos r0
          exact absurd this hg'
      · rw [ifn c]
  · apply Nat.le_trans _ (Nat.zero_le _)
    apply Nat.le_of_eq
    apply finSum_zero
    intro g'
    by_cases c : A.dump s g' = s ∧ some g ≠ some g'
    · cases Nat.eq_zero_or_pos (I.v i g') with
      | inl h0 => simp [h0]
      | inr hpos =>
        exfalso
        apply hex
        exact ⟨g', c.1, hpos, fun e => c.2 (by rw [e])⟩
    · rw [ifn c]

/-- **Main theorem**: dumping on any source of `D` yields a strong EFX₀ allocation. -/
theorem dump_efx0 (hI : I.TwoRelevant) (hP1 : A.P1) (hP2 : A.P2)
    (s : Fin I.n) (hsrc : A.IsSource s) : I.EFX0 (A.dump s) := by
  intro i j hij g hg
  by_cases hjs : j = s
  · rw [hjs] at hij hg ⊢
    rw [A.own_val s i hij]
    exact A.sink_val_le hI hP1 hP2 s hsrc i hij g
  · rw [A.other_val s i j hjs g hg]
    exact Nat.zero_le _

/-- **Branch A**: the sink is unassigned (`X_s = Z`); unassigned agents are always sources. -/
theorem dump_efx0_unassigned (hI : I.TwoRelevant) (hP1 : A.P1) (hP2 : A.P2)
    (s : Fin I.n) (hs : A.ρ s = none) : I.EFX0 (A.dump s) :=
  A.dump_efx0 hI hP1 hP2 s (A.unassigned_isSource s hs)

/-- **Branch B**: the sink is an assigned source (`X_s = {ρ(s)} ∪ Z`). -/
theorem dump_efx0_assigned (hI : I.TwoRelevant) (hP1 : A.P1) (hP2 : A.P2)
    (s : Fin I.n) (g : Fin I.m) (_hs : A.ρ s = some g) (hsrc : A.IsSource s) :
    I.EFX0 (A.dump s) :=
  A.dump_efx0 hI hP1 hP2 s hsrc

/-- **A well-founded envy relation has a source.** After Phase 2 the arc relation of `D` has no
directed cycle; on the finite type `Fin n` that is the same as well-foundedness of `fun i j => Arc i j`,
and a minimal element of a well-founded relation is exactly an agent nobody points at. -/
theorem wf_has_source (hn : 0 < I.n) (hwf : WellFounded A.Arc) : ∃ s, A.IsSource s := by
  have x : Fin I.n := ⟨0, hn⟩
  refine hwf.induction (C := fun _ => ∃ s, A.IsSource s) x ?_
  intro y ih
  by_cases hy : A.IsSource y
  · exact ⟨y, hy⟩
  · have : ∃ i, A.Arc i y := by
      apply Classical.byContradiction
      intro hne
      exact hy (fun i hi => hne ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := this
    exact ih i hi

end PAssign

/-! ## Executable algorithm, verified except for liveness -/

section Exec
variable (I : Inst)

abbrev Rho := Fin I.n → Option (Fin I.m)

/-- Some agent holds `g`. -/
def heldB (ρ : Rho I) (g : Fin I.m) : Bool := (findFin I.n (fun i => decide (ρ i = some g))).isSome

theorem heldB_false_iff (ρ : Rho I) (g : Fin I.m) : heldB I ρ g = false ↔ ∀ i, ρ i ≠ some g := by
  unfold heldB
  constructor
  · intro h i hi
    cases hf : findFin I.n (fun i => decide (ρ i = some g)) with
    | some i' => rw [hf] at h; simp at h
    | none =>
      have := findFin_none _ _ hf i
      simp at this
      exact this hi
  · intro h
    cases hf : findFin I.n (fun i => decide (ρ i = some g)) with
    | some i' =>
      have := findFin_some _ _ _ hf
      simp at this
      exact absurd this (h i')
    | none => rfl

theorem heldB_true_exists (ρ : Rho I) (g : Fin I.m) (h : heldB I ρ g = true) : ∃ j, ρ j = some g := by
  unfold heldB at h
  cases hf : findFin I.n (fun i => decide (ρ i = some g)) with
  | some j =>
    have := findFin_some _ _ _ hf
    simp at this
    exact ⟨j, this⟩
  | none => rw [hf] at h; simp at h

/-! ### Phase 1: greedy assignment -/

/-- Best unheld relevant good of `i` among goods with index `< t` (later index wins ties). -/
def bestUpto (ρ : Rho I) (i : Fin I.n) : (t : Nat) → t ≤ I.m → Option (Fin I.m)
  | 0, _ => none
  | t+1, h =>
    match bestUpto ρ i t (Nat.le_of_succ_le h) with
    | none => if heldB I ρ ⟨t, h⟩ = false ∧ 0 < I.v i ⟨t, h⟩ then some ⟨t, h⟩ else none
    | some g' =>
      if heldB I ρ ⟨t, h⟩ = false ∧ 0 < I.v i ⟨t, h⟩ ∧ I.v i g' < I.v i ⟨t, h⟩ then some ⟨t, h⟩ else some g'

theorem bestUpto_none (ρ : Rho I) (i : Fin I.n) : ∀ (t : Nat) (h : t ≤ I.m),
    bestUpto I ρ i t h = none → ∀ g : Fin I.m, g.val < t → heldB I ρ g = false → I.v i g = 0
  | 0, _, _, _, hg, _ => absurd hg (Nat.not_lt_zero _)
  | t+1, h, hn, g, hg, hu => by
    simp only [bestUpto] at hn
    split at hn
    · rename_i hacc
      split at hn
      · cases hn
      · rename_i hcond
        by_cases e : g.val = t
        · have hg' : g = ⟨t, h⟩ := Fin.ext e
          rw [hg'] at hu ⊢
          cases Nat.eq_zero_or_pos (I.v i ⟨t, h⟩) with
          | inl h0 => exact h0
          | inr hp => exact absurd ⟨hu, hp⟩ hcond
        · exact bestUpto_none ρ i t _ hacc g (by omega) hu
    · split at hn <;> cases hn

theorem bestUpto_some (ρ : Rho I) (i : Fin I.n) : ∀ (t : Nat) (h : t ≤ I.m) (g : Fin I.m),
    bestUpto I ρ i t h = some g →
      g.val < t ∧ heldB I ρ g = false ∧ 0 < I.v i g ∧
        ∀ g' : Fin I.m, g'.val < t → heldB I ρ g' = false → I.v i g' ≤ I.v i g
  | 0, _, g, hs => by simp [bestUpto] at hs
  | t+1, h, g, hs => by
    simp only [bestUpto] at hs
    split at hs
    · rename_i hacc
      split at hs
      · rename_i hcond
        cases hs
        refine ⟨Nat.lt_succ_self t, hcond.1, hcond.2, ?_⟩
        intro g' hg' hu'
        by_cases e : g'.val = t
        · have hg'' : g' = ⟨t, h⟩ := Fin.ext e
          subst hg''
          exact Nat.le_refl _
        · rw [bestUpto_none I ρ i t _ hacc g' (by omega) hu']
          exact Nat.zero_le _
      · cases hs
    · rename_i g0 hacc
      have ih := bestUpto_some ρ i t _ g0 hacc
      split at hs
      · rename_i hcond
        cases hs
        refine ⟨Nat.lt_succ_self t, hcond.1, hcond.2.1, ?_⟩
        intro g' hg' hu'
        by_cases e : g'.val = t
        · have hg'' : g' = ⟨t, h⟩ := Fin.ext e
          subst hg''
          exact Nat.le_refl _
        · exact Nat.le_trans (ih.2.2.2 g' (by omega) hu') (Nat.le_of_lt hcond.2.2)
      · rename_i hcond
        cases hs
        refine ⟨Nat.lt_succ_of_lt ih.1, ih.2.1, ih.2.2.1, ?_⟩
        intro g' hg' hu'
        by_cases e : g'.val = t
        · have hg'' : g' = ⟨t, h⟩ := Fin.ext e
          subst hg''
          apply Nat.le_of_not_lt
          intro hlt
          exact hcond ⟨hu', Nat.lt_of_le_of_lt (Nat.zero_le _) hlt, hlt⟩
        · exact ih.2.2.2 g' (by omega) hu'

def bestAvail (ρ : Rho I) (i : Fin I.n) : Option (Fin I.m) := bestUpto I ρ i I.m (Nat.le_refl _)

theorem bestAvail_none (ρ : Rho I) (i : Fin I.n) (h : bestAvail I ρ i = none) :
    ∀ g, heldB I ρ g = false → I.v i g = 0 :=
  fun g hu => bestUpto_none I ρ i I.m _ h g g.isLt hu

theorem bestAvail_some (ρ : Rho I) (i : Fin I.n) (g : Fin I.m) (h : bestAvail I ρ i = some g) :
    heldB I ρ g = false ∧ 0 < I.v i g ∧ ∀ g', heldB I ρ g' = false → I.v i g' ≤ I.v i g :=
  let r := bestUpto_some I ρ i I.m _ g h
  ⟨r.2.1, r.2.2.1, fun g' hu => r.2.2.2 g' g'.isLt hu⟩

/-- One greedy step: agent `i` takes its best available relevant good, if any. -/
def step (ρ : Rho I) (i : Fin I.n) : Rho I :=
  match bestAvail I ρ i with
  | some g => fun k => if k = i then some g else ρ k
  | none => ρ

/-- Process agents `0, 1, …, t-1` in order. -/
def phase1Upto : (t : Nat) → t ≤ I.n → Rho I
  | 0, _ => fun _ => none
  | t+1, h => step I (phase1Upto t (Nat.le_of_succ_le h)) ⟨t, h⟩

def phase1 : Rho I := phase1Upto I I.n (Nat.le_refl _)

/-- The invariants maintained by the algorithm (relevance, injectivity, (P1), (P2)). -/
structure Inv (ρ : Rho I) : Prop where
  rel : ∀ i g, ρ i = some g → 0 < I.v i g
  inj : ∀ i j g, ρ i = some g → ρ j = some g → i = j
  p1 : ∀ i, ρ i = none → ∀ g, 0 < I.v i g → ∃ j, ρ j = some g
  p2 : ∀ i g, ρ i = some g → ∀ g', (∀ j, ρ j ≠ some g') → I.v i g' ≤ I.v i g

/-- The invariants after processing agents of index `< t`. -/
structure InvUpto (t : Nat) (ρ : Rho I) : Prop where
  rel : ∀ i g, ρ i = some g → 0 < I.v i g
  inj : ∀ i j g, ρ i = some g → ρ j = some g → i = j
  p1 : ∀ i : Fin I.n, i.val < t → ρ i = none → ∀ g, 0 < I.v i g → ∃ j, ρ j = some g
  p2 : ∀ i g, ρ i = some g → ∀ g', (∀ j, ρ j ≠ some g') → I.v i g' ≤ I.v i g
  unproc : ∀ i : Fin I.n, t ≤ i.val → ρ i = none
  /-- Nobody prefers a good held by a later-processed agent: arcs of `D` point backwards. -/
  later : ∀ i g, ρ i = some g → ∀ j g', ρ j = some g' → i.val < j.val → I.v i g' ≤ I.v i g
  /-- Holders of a processed-but-unassigned agent's relevant goods were processed earlier. -/
  holders : ∀ x : Fin I.n, x.val < t → ρ x = none → ∀ g, 0 < I.v x g → ∀ y, ρ y = some g → y.val < x.val

theorem step_inv (t : Nat) (ρ : Rho I) (hρ : InvUpto I t ρ) (i : Fin I.n) (hi : i.val = t) :
    InvUpto I (t+1) (step I ρ i) := by
  have hnone : ρ i = none := hρ.unproc i (by omega)
  unfold step
  cases hb : bestAvail I ρ i with
  | none =>
    have hn := bestAvail_none I ρ i hb
    show InvUpto I (t+1) ρ
    refine ⟨hρ.rel, hρ.inj, ?_, hρ.p2, ?_, hρ.later, ?_⟩
    · intro i' hlt h0 g hg
      by_cases e : i'.val = t
      · have e' : i' = i := Fin.ext (by omega)
        subst e'
        cases hh : heldB I ρ g with
        | true => exact heldB_true_exists I ρ g hh
        | false =>
          have := hn g hh
          rw [this] at hg
          exact absurd hg (Nat.lt_irrefl 0)
      · exact hρ.p1 i' (by omega) h0 g hg
    · intro i' hle
      exact hρ.unproc i' (by omega)
    · intro x hx h0 g hg y hy
      by_cases e : x.val = t
      · apply Nat.lt_of_not_le
        intro hle
        have : ρ y = none := hρ.unproc y (by omega)
        rw [this] at hy
        cases hy
      · exact hρ.holders x (by omega) h0 g hg y hy
  | some g =>
    obtain ⟨hu, hpos, hbest⟩ := bestAvail_some I ρ i g hb
    have hu' : ∀ j, ρ j ≠ some g := (heldB_false_iff I ρ g).mp hu
    show InvUpto I (t+1) (fun k => if k = i then some g else ρ k)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k g' hk
      change (if k = i then some g else ρ k) = some g' at hk
      by_cases e : k = i
      · rw [ifp e] at hk
        cases hk
        rw [e]
        exact hpos
      · rw [ifn e] at hk
        exact hρ.rel k g' hk
    · intro k k' g' hk hk'
      change (if k = i then some g else ρ k) = some g' at hk
      change (if k' = i then some g else ρ k') = some g' at hk'
      by_cases e : k = i
      · by_cases e' : k' = i
        · rw [e, e']
        · rw [ifp e] at hk
          rw [ifn e'] at hk'
          cases hk
          exact absurd hk' (hu' k')
      · by_cases e' : k' = i
        · rw [ifn e] at hk
          rw [ifp e'] at hk'
          cases hk'
          exact absurd hk (hu' k)
        · rw [ifn e] at hk
          rw [ifn e'] at hk'
          exact hρ.inj k k' g' hk hk'
    · intro i' hlt h0 g' hg'
      change (if i' = i then some g else ρ i') = none at h0
      by_cases e : i' = i
      · rw [ifp e] at h0
        cases h0
      · rw [ifn e] at h0
        have hlt' : i'.val < t := by
          have : i'.val ≠ t := fun ee => e (Fin.ext (by omega))
          omega
        obtain ⟨j, hj⟩ := hρ.p1 i' hlt' h0 g' hg'
        have hj' : j ≠ i := by
          intro ee
          rw [ee, hnone] at hj
          cases hj
        exact ⟨j, by show (if j = i then some g else ρ j) = some g'; rw [ifn hj']; exact hj⟩
    · intro k g0 hk g' hun
      change (if k = i then some g else ρ k) = some g0 at hk
      have hunρ : ∀ j, ρ j ≠ some g' := by
        intro j hj
        by_cases e : j = i
        · rw [e, hnone] at hj
          cases hj
        · exact hun j (by show (if j = i then some g else ρ j) = some g'; rw [ifn e]; exact hj)
      by_cases e : k = i
      · rw [ifp e] at hk
        cases hk
        rw [e]
        exact hbest g' ((heldB_false_iff I ρ g').mpr hunρ)
      · rw [ifn e] at hk
        exact hρ.p2 k g0 hk g' hunρ
    · intro k hle
      have e : k ≠ i := by
        intro ee
        rw [ee] at hle
        omega
      show (if k = i then some g else ρ k) = none
      rw [ifn e]
      exact hρ.unproc k (by omega)
    · intro k g0 hk j g' hj hlt
      change (if k = i then some g else ρ k) = some g0 at hk
      change (if j = i then some g else ρ j) = some g' at hj
      by_cases ej : j = i
      · rw [ifp ej] at hj
        cases hj
        have ek : k ≠ i := fun e => by rw [e, ej] at hlt; exact Nat.lt_irrefl _ hlt
        rw [ifn ek] at hk
        exact hρ.p2 k g0 hk g hu'
      · rw [ifn ej] at hj
        by_cases ek : k = i
        · rw [ek, hi] at hlt
          have hj0 := hρ.unproc j (by omega)
          rw [hj0] at hj
          cases hj
        · rw [ifn ek] at hk
          exact hρ.later k g0 hk j g' hj hlt
    · intro x hx h0 g' hg' y hy
      change (if x = i then some g else ρ x) = none at h0
      change (if y = i then some g else ρ y) = some g' at hy
      by_cases ex : x = i
      · rw [ifp ex] at h0
        cases h0
      · rw [ifn ex] at h0
        have hx' : x.val < t := by
          have : x.val ≠ t := fun ee => ex (Fin.ext (by omega))
          omega
        by_cases ey : y = i
        · rw [ifp ey] at hy
          cases hy
          obtain ⟨j, hj⟩ := hρ.p1 x hx' h0 _ hg'
          exact absurd hj (hu' j)
        · rw [ifn ey] at hy
          exact hρ.holders x hx' h0 g' hg' y hy

theorem phase1Upto_inv : ∀ (t : Nat) (h : t ≤ I.n), InvUpto I t (phase1Upto I t h)
  | 0, _ =>
    ⟨fun _ _ hk => by simp [phase1Upto] at hk, fun _ _ _ hk => by simp [phase1Upto] at hk,
     fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ _ hk => by simp [phase1Upto] at hk, fun _ _ => rfl,
     fun _ _ hk => by simp [phase1Upto] at hk, fun _ hx => absurd hx (Nat.not_lt_zero _)⟩
  | t+1, h => step_inv I t _ (phase1Upto_inv t (Nat.le_of_succ_le h)) ⟨t, h⟩ rfl

theorem phase1_inv : Inv I (phase1 I) :=
  let h := phase1Upto_inv I I.n (Nat.le_refl _)
  ⟨h.rel, h.inj, fun i => h.p1 i i.isLt, h.p2⟩

/-! ### Phase 2: rotations along cycles, each checked at run time -/

def utilE (ρ : Rho I) (i : Fin I.n) : Nat :=
  match ρ i with
  | some g => I.v i g
  | none => 0

/-- Successor of `i` in `D` (the first out-arc). -/
def succE (ρ : Rho I) (i : Fin I.n) : Option (Fin I.n) :=
  findFin I.n (fun j =>
    match ρ j with
    | some g => decide (utilE I ρ i < I.v i g)
    | none => false)

theorem succE_some (ρ : Rho I) (i j : Fin I.n) (h : succE I ρ i = some j) :
    ∃ g, ρ j = some g ∧ utilE I ρ i < I.v i g := by
  have := findFin_some _ _ _ h
  cases hj : ρ j with
  | none => rw [hj] at this; simp at this
  | some g =>
    rw [hj] at this
    simp at this
    exact ⟨g, rfl, this⟩

def memB (k : Fin I.n) : List (Fin I.n) → Bool
  | [] => false
  | x :: xs => decide (k = x) || memB k xs

theorem memB_iff (k : Fin I.n) : ∀ l, memB I k l = true ↔ k ∈ l
  | [] => by simp [memB]
  | x :: xs => by simp [memB, memB_iff k xs]

def allB (p : Fin I.n → Bool) : List (Fin I.n) → Bool
  | [] => true
  | x :: xs => p x && allB p xs

theorem allB_true (p : Fin I.n → Bool) : ∀ l, allB I p l = true → ∀ x, x ∈ l → p x = true
  | [], _, x, hx => by simp at hx
  | x :: xs, h, y, hy => by
    simp only [allB, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact h.1
    · exact allB_true p xs h.2 y hy'

def anyB (p : Fin I.n → Bool) : List (Fin I.n) → Bool
  | [] => false
  | x :: xs => p x || anyB p xs

theorem anyB_true (p : Fin I.n → Bool) : ∀ l, anyB I p l = true → ∃ x, x ∈ l ∧ p x = true
  | [], h => by simp [anyB] at h
  | x :: xs, h => by
    simp only [anyB, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨x, List.mem_cons_self .., h⟩
    · obtain ⟨y, hy, hp⟩ := anyB_true p xs h
      exact ⟨y, List.mem_cons_of_mem x hy, hp⟩

/-- Rotate along `C`: every member takes the good of its successor in `D`. -/
def rotate (ρ : Rho I) (C : List (Fin I.n)) : Rho I := fun k =>
  if memB I k C = true then
    match succE I ρ k with
    | some j => ρ j
    | none => ρ k
  else ρ k

/-- Injectivity check. -/
def injB (ρ : Rho I) : Bool :=
  allFin I.n fun a => allFin I.n fun b =>
    if a = b then true else
    match ρ a with
    | none => true
    | some g => decide (ρ b ≠ some g)

theorem injB_sound (ρ : Rho I) (h : injB I ρ = true) :
    ∀ a b g, ρ a = some g → ρ b = some g → a = b := by
  intro a b g ha hb
  have h1 := allFin_true _ _ (allFin_true _ _ h a) b
  by_cases e : a = b
  · exact e
  · rw [ifn e, ha] at h1
    simp at h1
    exact absurd hb h1

/-- The run-time check on a candidate cycle `C`: every member is assigned, has its `D`-successor in
`C`, and is the successor of some member; and the rotated assignment is injective. -/
def nonemptyB : List (Fin I.n) → Bool
  | [] => false
  | _ :: _ => true

theorem nonemptyB_true (C : List (Fin I.n)) (h : nonemptyB I C = true) : ∃ k, k ∈ C := by
  cases C with
  | nil => cases h
  | cons x xs => exact ⟨x, List.mem_cons_self ..⟩

def validRot (ρ : Rho I) (C : List (Fin I.n)) : Bool :=
  nonemptyB I C &&
  allB I (fun k => (ρ k).isSome && (match succE I ρ k with | some j => memB I j C | none => false)) C &&
  allB I (fun i => anyB I (fun k => decide (succE I ρ k = some i)) C) C &&
  injB I (rotate I ρ C)

theorem rotate_inv (ρ : Rho I) (C : List (Fin I.n)) (hρ : Inv I ρ) (hv : validRot I ρ C = true) :
    Inv I (rotate I ρ C) := by
  simp only [validRot, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨_, h1⟩, h2⟩, h3⟩ := hv
  have hC1 : ∀ k, k ∈ C → (ρ k).isSome = true ∧ ∃ j, succE I ρ k = some j ∧ j ∈ C := by
    intro k hk
    have hh := allB_true I _ C h1 k hk
    simp only [Bool.and_eq_true] at hh
    refine ⟨hh.1, ?_⟩
    have hh2 := hh.2
    cases hs : succE I ρ k with
    | none => rw [hs] at hh2; change false = true at hh2; cases hh2
    | some j =>
      rw [hs] at hh2
      change memB I j C = true at hh2
      exact ⟨j, rfl, (memB_iff I j C).mp hh2⟩
  have hC2 : ∀ i, i ∈ C → ∃ k, k ∈ C ∧ succE I ρ k = some i := by
    intro i hi
    have hh := allB_true I _ C h2 i hi
    obtain ⟨k, hk, hk'⟩ := anyB_true I _ C hh
    exact ⟨k, hk, of_decide_eq_true hk'⟩
  have hrot_in : ∀ k, k ∈ C → ∀ j, succE I ρ k = some j → rotate I ρ C k = ρ j := by
    intro k hk j hj
    unfold rotate
    rw [ifp ((memB_iff I k C).mpr hk), hj]
  have hrot_out : ∀ k, ¬ k ∈ C → rotate I ρ C k = ρ k := by
    intro k hk
    unfold rotate
    rw [ifn (fun h => hk ((memB_iff I k C).mp h))]
  have hheld : ∀ g, (∃ j, ρ j = some g) → ∃ j, rotate I ρ C j = some g := by
    intro g hg
    obtain ⟨j, hj⟩ := hg
    by_cases hjC : j ∈ C
    · obtain ⟨k, hk, hk'⟩ := hC2 j hjC
      exact ⟨k, by rw [hrot_in k hk j hk', hj]⟩
    · exact ⟨j, by rw [hrot_out j hjC]; exact hj⟩
  have hun : ∀ g, (∀ j, rotate I ρ C j ≠ some g) → ∀ j, ρ j ≠ some g := by
    intro g h j hj
    obtain ⟨j', hj'⟩ := hheld g ⟨j, hj⟩
    exact h j' hj'
  have hnone : ∀ k, rotate I ρ C k = none → ρ k = none := by
    intro k hk
    by_cases hkC : k ∈ C
    · obtain ⟨hs, j, hj, _⟩ := hC1 k hkC
      obtain ⟨g, hg, _⟩ := succE_some I ρ k j hj
      rw [hrot_in k hkC j hj, hg] at hk
      cases hk
    · rw [hrot_out k hkC] at hk
      exact hk
  refine ⟨?_, injB_sound I _ h3, ?_, ?_⟩
  · intro k g hk
    by_cases hkC : k ∈ C
    · obtain ⟨_, j, hj, _⟩ := hC1 k hkC
      obtain ⟨g', hg', hlt⟩ := succE_some I ρ k j hj
      rw [hrot_in k hkC j hj, hg'] at hk
      cases hk
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    · rw [hrot_out k hkC] at hk
      exact hρ.rel k g hk
  · intro k hk g hg
    obtain ⟨j, hj⟩ := hρ.p1 k (hnone k hk) g hg
    exact hheld g ⟨j, hj⟩
  · intro k g hk g' hg'
    have hg'' := hun g' hg'
    by_cases hkC : k ∈ C
    · obtain ⟨hs, j, hj, _⟩ := hC1 k hkC
      obtain ⟨g0, hg0, hlt⟩ := succE_some I ρ k j hj
      rw [hrot_in k hkC j hj, hg0] at hk
      cases hk
      cases hk0 : ρ k with
      | none => rw [hk0] at hs; simp at hs
      | some h0 =>
        have hp2 := hρ.p2 k h0 hk0 g' hg''
        have hu : utilE I ρ k = I.v k h0 := by simp [utilE, hk0]
        rw [hu] at hlt
        exact Nat.le_of_lt (Nat.lt_of_le_of_lt hp2 hlt)
    · rw [hrot_out k hkC] at hk
      exact hρ.p2 k g hk g' hg''

/-- Cycle search (unverified; its result is checked by `validRot` before use). -/
def walk (ρ : Rho I) : Nat → Fin I.n → List (Fin I.n) → Option (Fin I.n)
  | 0, _, _ => none
  | fuel+1, x, seen =>
    if memB I x seen = true then some x else
    match succE I ρ x with
    | some y => walk ρ fuel y (x :: seen)
    | none => none

def cycleFrom (ρ : Rho I) : Nat → Fin I.n → Fin I.n → List (Fin I.n) → List (Fin I.n)
  | 0, _, _, acc => acc
  | fuel+1, start, x, acc =>
    match succE I ρ x with
    | some y => if y = start then x :: acc else cycleFrom ρ fuel start y (x :: acc)
    | none => acc

def findCycle (ρ : Rho I) : Option (List (Fin I.n)) :=
  match findFin I.n (fun x => (walk I ρ (I.n + 1) x []).isSome) with
  | none => none
  | some x =>
    match walk I ρ (I.n + 1) x [] with
    | some c => some (cycleFrom I ρ (I.n + 1) c c [])
    | none => none

/-- Tabulate an assignment (so that repeated rotations do not nest closures). -/
def materialize (ρ : Rho I) : Rho I :=
  let a : Array (Option (Fin I.m)) := Array.ofFn ρ
  fun k => a.getD k.val none

theorem materialize_eq (ρ : Rho I) : materialize I ρ = ρ := by
  funext k
  unfold materialize
  simp [Array.getD]

/-- Phase 2: rotate along found cycles while the run-time check passes. -/
def phase2 : Nat → Rho I → Rho I
  | 0, ρ => ρ
  | fuel+1, ρ =>
    match findCycle I ρ with
    | some C => if validRot I ρ C = true then phase2 fuel (materialize I (rotate I ρ C)) else ρ
    | none => ρ

theorem phase2_inv : ∀ (fuel : Nat) (ρ : Rho I), Inv I ρ → Inv I (phase2 I fuel ρ)
  | 0, _, h => h
  | fuel+1, ρ, h => by
    simp only [phase2]
    split
    · split
      · rw [materialize_eq]
        exact phase2_inv fuel _ (rotate_inv I ρ _ h (by assumption))
      · exact h
    · exact h

/-! ### Phase 3 and 4 -/

def hasArcE (ρ : Rho I) (i j : Fin I.n) : Bool :=
  match ρ j with
  | some g => decide (utilE I ρ i < I.v i g)
  | none => false

/-- The first source of `D`, if any. -/
def sourceE (ρ : Rho I) : Option (Fin I.n) :=
  findFin I.n (fun s => allFin I.n (fun i => !hasArcE I ρ i s))

theorem sourceE_some (ρ : Rho I) (s : Fin I.n) (h : sourceE I ρ = some s) :
    ∀ i, hasArcE I ρ i s = false := by
  intro i
  have := allFin_true _ _ (findFin_some _ _ _ h) i
  simpa using this

def dumpE (ρ : Rho I) (s : Fin I.n) : I.Alloc := fun g =>
  match findFin I.n (fun i => decide (ρ i = some g)) with
  | some j => j
  | none => s

/-- Total utility of an assignment and a crude upper bound for it (the fuel of Phase 2). -/
def totalU (ρ : Rho I) : Nat := finSum I.n (utilE I ρ)
def bound : Nat := finSum I.n (fun i => finSum I.m (fun g => I.v i g))

/-- The algorithm. Returns `none` only if a run-time check fails or no source is found. -/
def mrd : Option I.Alloc :=
  match sourceE I (phase2 I (bound I + 1) (phase1 I)) with
  | some s => some (dumpE I (phase2 I (bound I + 1) (phase1 I)) s)
  | none => none

/-! ### Soundness: whatever `mrd` returns is strongly EFX₀ -/

def toPAssign (ρ : Rho I) (h : Inv I ρ) : PAssign I := ⟨ρ, h.rel, h.inj⟩

theorem toPAssign_util (ρ : Rho I) (h : Inv I ρ) (i : Fin I.n) :
    (toPAssign I ρ h).util i = utilE I ρ i := rfl

theorem toPAssign_source (ρ : Rho I) (h : Inv I ρ) (s : Fin I.n) (hs : sourceE I ρ = some s) :
    (toPAssign I ρ h).IsSource s := by
  intro i harc
  obtain ⟨g, hg, hlt⟩ := harc
  have hh := sourceE_some I ρ s hs i
  unfold hasArcE at hh
  have hg' : ρ s = some g := hg
  rw [hg'] at hh
  simp at hh
  rw [toPAssign_util] at hlt
  exact Nat.not_lt.mpr hh hlt

theorem dumpE_eq (ρ : Rho I) (h : Inv I ρ) (s : Fin I.n) :
    dumpE I ρ s = (toPAssign I ρ h).dump s := rfl

/-- **Soundness of the executable**: every allocation it returns is strongly EFX₀. -/
theorem mrd_sound (hI : I.TwoRelevant) (X : I.Alloc) (h : mrd I = some X) : I.EFX0 X := by
  unfold mrd at h
  cases hs : sourceE I (phase2 I (bound I + 1) (phase1 I)) with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    cases h
    have hinv := phase2_inv I (bound I + 1) (phase1 I) (phase1_inv I)
    rw [dumpE_eq I _ hinv s]
    exact (toPAssign I _ hinv).dump_efx0 hI hinv.p1 hinv.p2 s (toPAssign_source I _ hinv s hs)

/-- Boolean checker for 2-relevance, with soundness. -/
def twoRelCheck : Bool :=
  allFin I.n fun i => allFin I.m fun g1 => allFin I.m fun g2 => allFin I.m fun g3 =>
    if g1 = g2 ∨ g1 = g3 ∨ g2 = g3 then true
    else !(decide (0 < I.v i g1) && decide (0 < I.v i g2) && decide (0 < I.v i g3))

theorem twoRelCheck_sound (h : twoRelCheck I = true) : I.TwoRelevant := by
  intro i g1 g2 g3 h12 h13 h23 p1 p2 p3
  have h1 := allFin_true _ _ (allFin_true _ _ (allFin_true _ _ (allFin_true _ _ h i) g1) g2) g3
  rw [ifn (by simp [h12, h13, h23])] at h1
  simp [p1, p2, p3] at h1

end Exec


/-! ## Liveness, part 1: if some agent is unassigned after Phase 1, `mrd` always returns -/

section Live
variable (I : Inst)

theorem allFin_of_forall (k : Nat) (p : Fin k → Bool) (h : ∀ i, p i = true) : allFin k p = true := by
  unfold allFin
  cases hf : findFin k (fun i => !p i) with
  | some j =>
    have := findFin_some _ _ _ hf
    simp [h j] at this
  | none => rfl

/-- A checked rotation keeps unassigned agents unassigned (members of `C` are assigned). -/
theorem rotate_none (ρ : Rho I) (C : List (Fin I.n)) (hv : validRot I ρ C = true) (k : Fin I.n)
    (hk : ρ k = none) : rotate I ρ C k = none := by
  unfold rotate
  by_cases hkC : memB I k C = true
  · simp only [validRot, Bool.and_eq_true] at hv
    have hh := allB_true I _ C hv.1.1.2 k ((memB_iff I k C).mp hkC)
    simp only [Bool.and_eq_true] at hh
    rw [hk] at hh
    simp at hh
  · rw [ifn hkC]
    exact hk

theorem phase2_none : ∀ (fuel : Nat) (ρ : Rho I) (k : Fin I.n), ρ k = none → phase2 I fuel ρ k = none
  | 0, _, _, h => h
  | fuel+1, ρ, k, h => by
    simp only [phase2]
    cases hc : findCycle I ρ with
    | none => exact h
    | some C =>
      show (if validRot I ρ C = true then phase2 I fuel (materialize I (rotate I ρ C)) else ρ) k = none
      by_cases hv : validRot I ρ C = true
      · rw [ifp hv]
        exact phase2_none fuel _ k (by rw [materialize_eq]; exact rotate_none I ρ C hv k h)
      · rw [ifn hv]
        exact h

/-- If some agent is a source, the source search succeeds. -/
theorem sourceE_isSome (ρ : Rho I) (s : Fin I.n) (hs : ∀ i, hasArcE I ρ i s = false) :
    (sourceE I ρ).isSome = true := by
  unfold sourceE
  cases hf : findFin I.n (fun s => allFin I.n (fun i => !hasArcE I ρ i s)) with
  | some _ => rfl
  | none =>
    exfalso
    have this : allFin I.n (fun i => !hasArcE I ρ i s) = false := findFin_none _ _ hf s
    rw [allFin_of_forall I.n _ (fun i => by simp [hs i])] at this
    cases this

/-- No arc targets an unassigned agent. -/
theorem hasArcE_none (ρ : Rho I) (i s : Fin I.n) (hs : ρ s = none) : hasArcE I ρ i s = false := by
  unfold hasArcE
  rw [hs]

/-- **Liveness in Case A**: an agent left unassigned by Phase 1 guarantees an output. -/
theorem mrd_total_of_unassigned (i : Fin I.n) (hi : phase1 I i = none) : (mrd I).isSome = true := by
  unfold mrd
  have h2 : phase2 I (bound I + 1) (phase1 I) i = none := phase2_none I (bound I + 1) (phase1 I) i hi
  have hsrc := sourceE_isSome I _ i (fun j => hasArcE_none I _ j i h2)
  cases hf : sourceE I (phase2 I (bound I + 1) (phase1 I)) with
  | some s => rfl
  | none => rw [hf] at hsrc; simp at hsrc

/-! ### Liveness, part 2: termination by the utility potential -/

theorem finSum_le_finSum (k : Nat) (f g : Fin k → Nat) (h : ∀ i, f i ≤ g i) :
    finSum k f ≤ finSum k g := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    simp only [finSum]
    exact Nat.add_le_add (ih _ _ (fun i => h _)) (h _)

theorem finSum_lt_finSum (k : Nat) (f g : Fin k → Nat) (h : ∀ i, f i ≤ g i) (i0 : Fin k)
    (hi : f i0 < g i0) : finSum k f < finSum k g := by
  induction k with
  | zero => exact Fin.elim0 i0
  | succ k ih =>
    simp only [finSum]
    rcases fin_cases k i0 with ⟨i', rfl⟩ | rfl
    · exact Nat.add_lt_add_of_lt_of_le (ih _ _ (fun i => h _) i' hi) (h _)
    · exact Nat.add_lt_add_of_le_of_lt (finSum_le_finSum k _ _ (fun i => h _)) hi

theorem le_finSum (k : Nat) (f : Fin k → Nat) (i : Fin k) : f i ≤ finSum k f := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    simp only [finSum]
    rcases fin_cases k i with ⟨i', rfl⟩ | rfl
    · exact Nat.le_trans (ih (fun i => f i.castSucc) i') (Nat.le_add_right _ _)
    · exact Nat.le_add_left _ _

theorem utilE_le (ρ : Rho I) (i : Fin I.n) : utilE I ρ i ≤ finSum I.m (fun g => I.v i g) := by
  unfold utilE
  cases ρ i with
  | none => exact Nat.zero_le _
  | some g => exact le_finSum I.m _ g

theorem totalU_le_bound (ρ : Rho I) : totalU I ρ ≤ bound I :=
  finSum_le_finSum I.n _ _ (utilE_le I ρ)

theorem rotate_in (ρ : Rho I) (C : List (Fin I.n)) (k j : Fin I.n) (hk : memB I k C = true)
    (hj : succE I ρ k = some j) : rotate I ρ C k = ρ j := by
  unfold rotate
  rw [ifp hk, hj]

theorem rotate_out (ρ : Rho I) (C : List (Fin I.n)) (k : Fin I.n) (hk : memB I k C = false) :
    rotate I ρ C k = ρ k := by
  unfold rotate
  simp [hk]

/-- What the run-time check guarantees about every member of the list. -/
theorem validRot_member (ρ : Rho I) (C : List (Fin I.n)) (hv : validRot I ρ C = true) (k : Fin I.n)
    (hk : k ∈ C) : ∃ j g, succE I ρ k = some j ∧ ρ j = some g ∧ utilE I ρ k < I.v k g := by
  simp only [validRot, Bool.and_eq_true] at hv
  have hh := allB_true I _ C hv.1.1.2 k hk
  simp only [Bool.and_eq_true] at hh
  have hh2 := hh.2
  cases hs : succE I ρ k with
  | none => rw [hs] at hh2; change false = true at hh2; cases hh2
  | some j =>
    obtain ⟨g, hg, hlt⟩ := succE_some I ρ k j hs
    exact ⟨j, g, rfl, hg, hlt⟩

theorem validRot_nonempty (ρ : Rho I) (C : List (Fin I.n)) (hv : validRot I ρ C = true) :
    ∃ k, k ∈ C := by
  simp only [validRot, Bool.and_eq_true] at hv
  exact nonemptyB_true I C hv.1.1.1

theorem utilE_rotate_in (ρ : Rho I) (C : List (Fin I.n)) (k j : Fin I.n) (g : Fin I.m)
    (hk : memB I k C = true) (hj : succE I ρ k = some j) (hg : ρ j = some g) :
    utilE I (rotate I ρ C) k = I.v k g := by
  simp [utilE, rotate_in I ρ C k j hk hj, hg]

theorem utilE_rotate_out (ρ : Rho I) (C : List (Fin I.n)) (k : Fin I.n) (hk : memB I k C = false) :
    utilE I (rotate I ρ C) k = utilE I ρ k := by
  simp [utilE, rotate_out I ρ C k hk]

/-- **Potential**: a checked rotation strictly increases the total utility. -/
theorem rotate_totalU_lt (ρ : Rho I) (C : List (Fin I.n)) (hv : validRot I ρ C = true) :
    totalU I ρ < totalU I (rotate I ρ C) := by
  obtain ⟨k0, hk0⟩ := validRot_nonempty I ρ C hv
  unfold totalU
  apply finSum_lt_finSum I.n _ _ ?_ k0 ?_
  · intro k
    by_cases hk : memB I k C = true
    · obtain ⟨j, g, hj, hg, hlt⟩ := validRot_member I ρ C hv k ((memB_iff I k C).mp hk)
      rw [utilE_rotate_in I ρ C k j g hk hj hg]
      exact Nat.le_of_lt hlt
    · rw [utilE_rotate_out I ρ C k (Bool.eq_false_iff.mpr hk)]
      exact Nat.le_refl _
  · obtain ⟨j, g, hj, hg, hlt⟩ := validRot_member I ρ C hv k0 hk0
    rw [utilE_rotate_in I ρ C k0 j g ((memB_iff I k0 C).mpr hk0) hj hg]
    exact hlt

/-- A checked rotation keeps every agent assigned. -/
theorem rotate_assigned (ρ : Rho I) (C : List (Fin I.n)) (hv : validRot I ρ C = true)
    (hall : ∀ i, ρ i ≠ none) : ∀ i, rotate I ρ C i ≠ none := by
  intro i hi
  by_cases hk : memB I i C = true
  · obtain ⟨j, g, hj, hg, _⟩ := validRot_member I ρ C hv i ((memB_iff I i C).mp hk)
    rw [rotate_in I ρ C i j hk hj, hg] at hi
    cases hi
  · rw [rotate_out I ρ C i (Bool.eq_false_iff.mpr hk)] at hi
    exact hall i hi

/-- **The single remaining obligation**: on an assignment satisfying the invariants in which
everyone is assigned and no source exists, the cycle search returns a list that passes the
run-time check. (Exercised on every small instance by the exhaustive sweeps.) -/
def SearchOK : Prop :=
  ∀ ρ : Rho I, Inv I ρ → (∀ i, ρ i ≠ none) → sourceE I ρ = none →
    ∃ C, findCycle I ρ = some C ∧ validRot I ρ C = true

/-- **Termination**: with enough fuel, Phase 2 reaches a state with a source, given `SearchOK`. -/
theorem phase2_source (hS : SearchOK I) :
    ∀ (fuel : Nat) (ρ : Rho I), Inv I ρ → (∀ i, ρ i ≠ none) → bound I - totalU I ρ < fuel →
      (sourceE I (phase2 I fuel ρ)).isSome = true
  | 0, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | fuel+1, ρ, hinv, hall, hf => by
    simp only [phase2]
    cases hc : findCycle I ρ with
    | none =>
      show (sourceE I ρ).isSome = true
      cases hs : sourceE I ρ with
      | some _ => rfl
      | none =>
        obtain ⟨C, hC, _⟩ := hS ρ hinv hall hs
        rw [hC] at hc
        cases hc
    | some C =>
      show (sourceE I (if validRot I ρ C = true then phase2 I fuel (materialize I (rotate I ρ C)) else ρ)).isSome = true
      by_cases hv : validRot I ρ C = true
      · rw [ifp hv, materialize_eq]
        have hlt := rotate_totalU_lt I ρ C hv
        have hb := totalU_le_bound I (rotate I ρ C)
        exact phase2_source hS fuel _ (rotate_inv I ρ C hinv hv) (rotate_assigned I ρ C hv hall) (by omega)
      · rw [ifn hv]
        cases hs : sourceE I ρ with
        | some _ => rfl
        | none =>
          obtain ⟨C', hC', hv'⟩ := hS ρ hinv hall hs
          rw [hc] at hC'
          cases hC'
          exact absurd hv' hv

/-- **Liveness in Case B**, conditional only on `SearchOK`. -/
theorem mrd_total_all_assigned (hS : SearchOK I) (hall : ∀ i, phase1 I i ≠ none) :
    (mrd I).isSome = true := by
  unfold mrd
  have hsrc := phase2_source I hS (bound I + 1) (phase1 I) (phase1_inv I) hall
    (by have := totalU_le_bound I (phase1 I); omega)
  cases hf : sourceE I (phase2 I (bound I + 1) (phase1 I)) with
  | some s => rfl
  | none => rw [hf] at hsrc; simp at hsrc

/-- **Liveness**, conditional only on `SearchOK`. -/
theorem mrd_total (hS : SearchOK I) : (mrd I).isSome = true := by
  by_cases h : ∃ i, phase1 I i = none
  · obtain ⟨i, hi⟩ := h
    exact mrd_total_of_unassigned I i hi
  · exact mrd_total_all_assigned I hS (fun i hi => h ⟨i, hi⟩)

end Live

/-! ## Array-backed executable (same algorithm, no closure chains), proved equal to `mrd` -/

section Arr
variable (I : Inst)

abbrev RhoA := Array (Option (Fin I.m))

def get (a : RhoA I) : Rho I := fun k => a.getD k.val none
def ofRho (ρ : Rho I) : RhoA I := Array.ofFn ρ

theorem get_ofRho (ρ : Rho I) : get I (ofRho I ρ) = ρ := by
  funext k
  unfold get ofRho
  simp [Array.getD]

def phase1A : (t : Nat) → t ≤ I.n → RhoA I
  | 0, _ => ofRho I (fun _ => none)
  | t+1, h => ofRho I (step I (get I (phase1A t (Nat.le_of_succ_le h))) ⟨t, h⟩)

theorem get_phase1A : ∀ (t : Nat) (h : t ≤ I.n), get I (phase1A I t h) = phase1Upto I t h
  | 0, _ => by simp only [phase1A, phase1Upto]; exact get_ofRho I _
  | t+1, h => by
    simp only [phase1A, phase1Upto]
    rw [get_ofRho, get_phase1A t]

def phase2A : Nat → RhoA I → RhoA I
  | 0, a => a
  | fuel+1, a =>
    match findCycle I (get I a) with
    | some C => if validRot I (get I a) C = true then phase2A fuel (ofRho I (rotate I (get I a) C)) else a
    | none => a

theorem get_phase2A : ∀ (fuel : Nat) (a : RhoA I), get I (phase2A I fuel a) = phase2 I fuel (get I a)
  | 0, _ => rfl
  | fuel+1, a => by
    simp only [phase2A, phase2]
    cases hc : findCycle I (get I a) with
    | none => rfl
    | some C =>
      show get I (if validRot I (get I a) C = true then phase2A I fuel (ofRho I (rotate I (get I a) C)) else a)
        = (if validRot I (get I a) C = true then phase2 I fuel (materialize I (rotate I (get I a) C)) else get I a)
      by_cases hv : validRot I (get I a) C = true
      · rw [ifp hv, ifp hv, get_phase2A fuel, materialize_eq, get_ofRho]
      · rw [ifn hv, ifn hv]

/-- The array-backed algorithm. -/
def mrdA : Option I.Alloc :=
  let a := phase2A I (bound I + 1) (phase1A I I.n (Nat.le_refl _))
  match sourceE I (get I a) with
  | some s => some (dumpE I (get I a) s)
  | none => none

theorem mrdA_eq : mrdA I = mrd I := by
  simp only [mrdA, mrd, phase1, get_phase2A, get_phase1A]

theorem mrdA_sound (hI : I.TwoRelevant) (X : I.Alloc) (h : mrdA I = some X) : I.EFX0 X :=
  mrd_sound I hI X (by rw [← mrdA_eq]; exact h)

theorem mrdA_total (hS : SearchOK I) : (mrdA I).isSome = true := by
  rw [mrdA_eq]; exact mrd_total I hS

end Arr

/-! ## The simplified algorithm: greedy Phase 1, then sink = first unassigned agent, else the last agent.
No rotations, no fuel, no run-time checks — and no `sorry`. -/

section Simple
variable (I : Inst)

theorem phase1_later (i : Fin I.n) (g : Fin I.m) (hi : phase1 I i = some g) (j : Fin I.n) (g' : Fin I.m)
    (hj : phase1 I j = some g') (hlt : i.val < j.val) : I.v i g' ≤ I.v i g :=
  (phase1Upto_inv I I.n (Nat.le_refl _)).later i g hi j g' hj hlt

def firstUnassigned (ρ : Rho I) : Option (Fin I.n) := findFin I.n (fun i => decide (ρ i = none))

def lastAgent (hn : 0 < I.n) : Fin I.n := ⟨I.n - 1, Nat.sub_lt hn Nat.one_pos⟩

/-- The simplified algorithm. -/
def mrdG (hn : 0 < I.n) : I.Alloc :=
  match firstUnassigned I (phase1 I) with
  | some s => dumpE I (phase1 I) s
  | none => dumpE I (phase1 I) (lastAgent I hn)

/-- **The last-processed agent is a source** when everybody is assigned: an arc `i → last` would mean
`i` prefers a good held by a later-processed agent, contradicting `phase1_later`. -/
theorem lastAgent_source (hn : 0 < I.n) (hall : ∀ i, phase1 I i ≠ none) :
    (toPAssign I (phase1 I) (phase1_inv I)).IsSource (lastAgent I hn) := by
  intro i harc
  obtain ⟨g, hg, hlt⟩ := harc
  have hg' : phase1 I (lastAgent I hn) = some g := hg
  rw [toPAssign_util] at hlt
  cases hi : phase1 I i with
  | none => exact hall i hi
  | some g0 =>
    have hu : utilE I (phase1 I) i = I.v i g0 := by simp [utilE, hi]
    rw [hu] at hlt
    by_cases e : i = lastAgent I hn
    · rw [e, hg'] at hi
      cases hi
      exact Nat.lt_irrefl _ hlt
    · have hlt' : i.val < (lastAgent I hn).val := by
        have h1 : i.val ≠ I.n - 1 := fun h => e (Fin.ext h)
        have h2 := i.isLt
        show i.val < I.n - 1
        omega
      exact absurd hlt (Nat.not_lt.mpr (phase1_later I i g0 hi (lastAgent I hn) g hg' hlt'))

/-- **Fully verified end-to-end theorem**: on every 2-relevant instance with at least one agent, the
simplified algorithm outputs a complete strongly-EFX₀ allocation. -/
theorem mrdG_efx0 (hI : I.TwoRelevant) (hn : 0 < I.n) : I.EFX0 (mrdG I hn) := by
  unfold mrdG
  have hinv := phase1_inv I
  cases hf : firstUnassigned I (phase1 I) with
  | some s =>
    show I.EFX0 (dumpE I (phase1 I) s)
    have hs : phase1 I s = none := by
      have := findFin_some _ _ _ hf
      simpa using this
    rw [dumpE_eq I _ hinv s]
    exact (toPAssign I _ hinv).dump_efx0 hI hinv.p1 hinv.p2 s ((toPAssign I _ hinv).unassigned_isSource s hs)
  | none =>
    have hall : ∀ i, phase1 I i ≠ none := by
      intro i hi
      have := findFin_none _ _ hf i
      simp at this
      exact this hi
    show I.EFX0 (dumpE I (phase1 I) (lastAgent I hn))
    rw [dumpE_eq I _ hinv (lastAgent I hn)]
    exact (toPAssign I _ hinv).dump_efx0 hI hinv.p1 hinv.p2 _ (lastAgent_source I hn hall)

/-- Array-backed version for native execution, proved equal. (Wrapped in `Option` so that the
compiler does not eta-expand it and recompute Phase 1 on every lookup.) -/
def mrdGA (hn : 0 < I.n) : Option I.Alloc :=
  let a := phase1A I I.n (Nat.le_refl _)
  some (match firstUnassigned I (get I a) with
    | some s => dumpE I (get I a) s
    | none => dumpE I (get I a) (lastAgent I hn))

theorem mrdGA_eq (hn : 0 < I.n) : mrdGA I hn = some (mrdG I hn) := by
  simp only [mrdGA, mrdG, phase1, get_phase1A]

theorem mrdGA_efx0 (hI : I.TwoRelevant) (hn : 0 < I.n) (X : I.Alloc) (h : mrdGA I hn = some X) :
    I.EFX0 X := by
  rw [mrdGA_eq] at h
  cases h
  exact mrdG_efx0 I hI hn

end Simple

/-! ## Closing the definitional gaps: counting hypothesis, checker completeness, existence, shape -/

section Bridge
variable (I : Inst)

theorem finSum_add (k : Nat) (f g : Fin k → Nat) :
    finSum k (fun i => f i + g i) = finSum k f + finSum k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

/-- Indicator of one index. -/
def ind (k : Nat) (x : Fin k) : Fin k → Nat := fun g => if g = x then 1 else 0

theorem finSum_ind (k : Nat) (x : Fin k) : finSum k (ind k x) = 1 := by
  rw [finSum_eq_single k (ind k x) x]
  · simp [ind]
  · intro i hi
    simp [ind, hi]

/-- The counting form of 2-relevance used in the write-up: `|R_i| ≤ 2`. -/
def numRelevant (i : Fin I.n) : Nat := finSum I.m (fun g => if 0 < I.v i g then 1 else 0)

/-- `|R_i| ≤ 2` for all `i` implies the formal hypothesis (no three distinct positive goods). -/
theorem twoRelevant_of_count (h : ∀ i, numRelevant I i ≤ 2) : I.TwoRelevant := by
  intro i g1 g2 g3 h12 h13 h23 p1 p2 p3
  have hle : finSum I.m (fun g => ind I.m g1 g + ind I.m g2 g + ind I.m g3 g) ≤ numRelevant I i := by
    unfold numRelevant
    apply finSum_le_finSum
    intro g
    by_cases e1 : g = g1
    · subst e1; simp [ind, h12, h13, p1]
    · by_cases e2 : g = g2
      · subst e2; simp [ind, Ne.symm h12, h23, p2]
      · by_cases e3 : g = g3
        · subst e3; simp [ind, Ne.symm h13, Ne.symm h23, p3]
        · simp [ind, e1, e2, e3]
  have h3 : finSum I.m (fun g => ind I.m g1 g + ind I.m g2 g + ind I.m g3 g) = 3 := by
    have ha : finSum I.m (fun g => ind I.m g1 g + ind I.m g2 g + ind I.m g3 g)
        = finSum I.m (fun g => ind I.m g1 g + ind I.m g2 g) + finSum I.m (ind I.m g3) :=
      finSum_add I.m _ _
    have hb : finSum I.m (fun g => ind I.m g1 g + ind I.m g2 g)
        = finSum I.m (ind I.m g1) + finSum I.m (ind I.m g2) :=
      finSum_add I.m _ _
    rw [ha, hb, finSum_ind, finSum_ind, finSum_ind]
  have := h i
  omega

/-- The Boolean checker is complete as well as sound. -/
theorem efx0Check_complete (X : I.Alloc) (h : I.EFX0 X) : I.efx0Check X = true := by
  unfold Inst.efx0Check
  apply allFin_of_forall
  intro i
  apply allFin_of_forall
  intro j
  by_cases hij : i = j
  · rw [ifp hij]
  · rw [ifn hij]
    apply allFin_of_forall
    intro g
    by_cases hg : X g = j
    · rw [ifp hg]
      exact decide_eq_true (h i j hij g hg)
    · rw [ifn hg]

theorem efx0Check_iff (X : I.Alloc) : I.efx0Check X = true ↔ I.EFX0 X :=
  ⟨Inst.efx0Check_sound I X, efx0Check_complete I X⟩

/-- **Existence**, under the formal hypothesis and under the counting hypothesis of the write-up. -/
theorem exists_efx0 (hI : I.TwoRelevant) (hn : 0 < I.n) : ∃ X : I.Alloc, I.EFX0 X :=
  ⟨mrdG I hn, mrdG_efx0 I hI hn⟩

theorem exists_efx0_of_count (h : ∀ i, numRelevant I i ≤ 2) (hn : 0 < I.n) : ∃ X : I.Alloc, I.EFX0 X :=
  exists_efx0 I (twoRelevant_of_count I h) hn

theorem dump_thin_other (A : PAssign I) (s j : Fin I.n) (hjs : j ≠ s) (g g' : Fin I.m)
    (hg : A.dump s g = j) (hg' : A.dump s g' = j) : g = g' := by
  have e1 := (A.dump_eq_iff s j hjs g).mp hg
  have e2 := (A.dump_eq_iff s j hjs g').mp hg'
  rw [e1] at e2
  exact Option.some.inj e2

/-- **Shape**: in the output, every bundle except one has at most one good. -/
theorem mrdG_shape (hn : 0 < I.n) :
    ∃ s, ∀ j, j ≠ s → ∀ g g', mrdG I hn g = j → mrdG I hn g' = j → g = g' := by
  unfold mrdG
  cases hf : firstUnassigned I (phase1 I) with
  | some s =>
    show ∃ s', ∀ j, j ≠ s' → ∀ g g', dumpE I (phase1 I) s g = j → dumpE I (phase1 I) s g' = j → g = g'
    refine ⟨s, fun j hjs g g' hg hg' => ?_⟩
    rw [dumpE_eq I _ (phase1_inv I) s] at hg hg'
    exact dump_thin_other I _ s j hjs g g' hg hg'
  | none =>
    show ∃ s', ∀ j, j ≠ s' → ∀ g g', dumpE I (phase1 I) (lastAgent I hn) g = j →
      dumpE I (phase1 I) (lastAgent I hn) g' = j → g = g'
    refine ⟨lastAgent I hn, fun j hjs g g' hg hg' => ?_⟩
    rw [dumpE_eq I _ (phase1_inv I) (lastAgent I hn)] at hg hg'
    exact dump_thin_other I _ (lastAgent I hn) j hjs g g' hg hg'

end Bridge

/-! ## Unconditional liveness of the rotation-based variant: after greedy Phase 1 there is no cycle -/

section NoCycle
variable (I : Inst)

theorem phase1_holders (x : Fin I.n) (hx : phase1 I x = none) (g : Fin I.m) (hg : 0 < I.v x g)
    (y : Fin I.n) (hy : phase1 I y = some g) : y.val < x.val :=
  (phase1Upto_inv I I.n (Nat.le_refl _)).holders x x.isLt hx g hg y hy

/-- Every arc of `D` after Phase 1 points to an earlier-processed agent. -/
theorem succE_lt (x y : Fin I.n) (h : succE I (phase1 I) x = some y) : y.val < x.val := by
  obtain ⟨g, hg, hlt⟩ := succE_some I (phase1 I) x y h
  cases hx : phase1 I x with
  | none =>
    have hpos : 0 < I.v x g := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    exact phase1_holders I x hx g hpos y hg
  | some g0 =>
    have hu : utilE I (phase1 I) x = I.v x g0 := by simp [utilE, hx]
    rw [hu] at hlt
    apply Nat.lt_of_not_le
    intro hle
    cases Nat.eq_or_lt_of_le hle with
    | inl e =>
      have exy : x = y := Fin.ext e
      rw [exy, hg] at hx
      cases hx
      exact Nat.lt_irrefl _ hlt
    | inr hlt2 => exact absurd hlt (Nat.not_lt.mpr (phase1_later I x g0 hx y g hg hlt2))

/-- The forward walk never revisits a vertex: indices strictly decrease. -/
theorem walk_none : ∀ (fuel : Nat) (x : Fin I.n) (seen : List (Fin I.n)),
    (∀ z, z ∈ seen → x.val < z.val) → walk I (phase1 I) fuel x seen = none
  | 0, _, _, _ => rfl
  | fuel+1, x, seen, hseen => by
    simp only [walk]
    have hx : memB I x seen = false := by
      apply Bool.eq_false_iff.mpr
      intro hm
      exact Nat.lt_irrefl _ (hseen x ((memB_iff I x seen).mp hm))
    rw [hx, ifn (by decide : ¬ (false = true))]
    cases hs : succE I (phase1 I) x with
    | none => rfl
    | some y =>
      show walk I (phase1 I) fuel y (x :: seen) = none
      apply walk_none fuel y (x :: seen)
      intro z hz
      have hyx := succE_lt I x y hs
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact hyx
      · exact Nat.lt_trans hyx (hseen z hz')

theorem findCycle_phase1 : findCycle I (phase1 I) = none := by
  unfold findCycle
  have h : findFin I.n (fun x => (walk I (phase1 I) (I.n + 1) x []).isSome) = none := by
    cases hf : findFin I.n (fun x => (walk I (phase1 I) (I.n + 1) x []).isSome) with
    | none => rfl
    | some x =>
      have this : (walk I (phase1 I) (I.n + 1) x []).isSome = true := findFin_some _ _ _ hf
      rw [walk_none I (I.n + 1) x [] (fun z hz => by simp at hz)] at this
      simp at this
  rw [h]

/-- Phase 2 is the identity after a greedy Phase 1. -/
theorem phase2_phase1 : ∀ fuel : Nat, phase2 I fuel (phase1 I) = phase1 I
  | 0 => rfl
  | fuel+1 => by simp only [phase2, findCycle_phase1]

theorem hasArcE_false_of_source (ρ : Rho I) (h : Inv I ρ) (s : Fin I.n)
    (hs : (toPAssign I ρ h).IsSource s) : ∀ i, hasArcE I ρ i s = false := by
  intro i
  apply Bool.eq_false_iff.mpr
  intro ht
  unfold hasArcE at ht
  cases hg : ρ s with
  | none => rw [hg] at ht; change false = true at ht; cases ht
  | some g =>
    rw [hg] at ht
    simp at ht
    exact hs i ⟨g, hg, by rw [toPAssign_util]; exact ht⟩

/-- **Unconditional liveness** of the rotation-based executable. -/
theorem mrd_total_unconditional (hn : 0 < I.n) : (mrd I).isSome = true := by
  unfold mrd
  rw [phase2_phase1]
  have hsrc : (sourceE I (phase1 I)).isSome = true := by
    cases hf : firstUnassigned I (phase1 I) with
    | some s =>
      have hs : phase1 I s = none := by
        have := findFin_some _ _ _ hf
        simpa using this
      exact sourceE_isSome I _ s (fun j => hasArcE_none I _ j s hs)
    | none =>
      have hall : ∀ i, phase1 I i ≠ none := by
        intro i hi
        have := findFin_none _ _ hf i
        simp at this
        exact this hi
      exact sourceE_isSome I _ (lastAgent I hn)
        (hasArcE_false_of_source I _ (phase1_inv I) _ (lastAgent_source I hn hall))
  cases hf : sourceE I (phase1 I) with
  | some s => rfl
  | none => rw [hf] at hsrc; simp at hsrc

/-- The rotation-based executable always returns, and what it returns is EFX₀. -/
theorem mrd_correct (hI : I.TwoRelevant) (hn : 0 < I.n) : ∃ X, mrd I = some X ∧ I.EFX0 X := by
  have h := mrd_total_unconditional I hn
  cases hm : mrd I with
  | none => rw [hm] at h; simp at h
  | some X => exact ⟨X, rfl, mrd_sound I hI X hm⟩

end NoCycle

/-! ## Specification-level statements: independent of tie-breaking, and the headline theorem -/

section Spec
variable (I : Inst)

/-- The last agent is a source for *any* assignment with the Phase-1 invariants, however ties were
broken. -/
theorem lastAgent_source_gen (ρ : Rho I) (hinv : Inv I ρ)
    (hlater : ∀ i g, ρ i = some g → ∀ j g', ρ j = some g' → i.val < j.val → I.v i g' ≤ I.v i g)
    (hn : 0 < I.n) (hall : ∀ i, ρ i ≠ none) : (toPAssign I ρ hinv).IsSource (lastAgent I hn) := by
  intro i harc
  obtain ⟨g, hg, hlt⟩ := harc
  have hg' : ρ (lastAgent I hn) = some g := hg
  rw [toPAssign_util] at hlt
  cases hi : ρ i with
  | none => exact hall i hi
  | some g0 =>
    have hu : utilE I ρ i = I.v i g0 := by simp [utilE, hi]
    rw [hu] at hlt
    by_cases e : i = lastAgent I hn
    · rw [e, hg'] at hi
      cases hi
      exact Nat.lt_irrefl _ hlt
    · have hlt' : i.val < (lastAgent I hn).val := by
        have h1 : i.val ≠ I.n - 1 := fun h => e (Fin.ext h)
        have h2 := i.isLt
        show i.val < I.n - 1
        omega
      exact absurd hlt (Nat.not_lt.mpr (hlater i g0 hi (lastAgent I hn) g hg' hlt'))

/-- **Tie-breaking independence.** Any assignment satisfying (P1)–(P3) — i.e. any run of the greedy
Phase 1 with arbitrary tie-breaking — dumped on an unassigned agent or else on the last agent,
is strongly EFX₀. -/
theorem efx0_of_invariants (hI : I.TwoRelevant) (ρ : Rho I) (hinv : Inv I ρ)
    (hlater : ∀ i g, ρ i = some g → ∀ j g', ρ j = some g' → i.val < j.val → I.v i g' ≤ I.v i g)
    (hn : 0 < I.n) (s : Fin I.n)
    (hs : ρ s = none ∨ ((∀ i, ρ i ≠ none) ∧ s = lastAgent I hn)) :
    I.EFX0 (dumpE I ρ s) := by
  rw [dumpE_eq I ρ hinv s]
  apply (toPAssign I ρ hinv).dump_efx0 hI hinv.p1 hinv.p2 s
  rcases hs with hs | ⟨hall, rfl⟩
  · exact (toPAssign I ρ hinv).unassigned_isSource s hs
  · exact lastAgent_source_gen I ρ hinv hlater hn hall

/-- **Headline theorem.** For every additive instance with at least one agent in which every agent
values at most two goods positively, there is a complete strongly-EFX₀ allocation in which all
bundles but one contain at most one good. -/
theorem main_theorem (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 2) :
    ∃ X : I.Alloc, I.EFX0 X ∧ ∃ s, ∀ j, j ≠ s → ∀ g g', X g = j → X g' = j → g = g' :=
  ⟨mrdG I hn, mrdG_efx0 I (twoRelevant_of_count I h) hn, mrdG_shape I hn⟩

end Spec

/-! ## Worked examples, at the `Prop` level -/

def exInst : Inst where
  n := 3
  m := 5
  v := fun i g =>
    match i.val, g.val with
    | 0, 0 => 2 | 0, 1 => 5
    | 1, 1 => 1 | 1, 2 => 6
    | 2, 2 => 2 | 2, 0 => 7
    | _, _ => 0

/-- The algorithm terminates with an allocation on the worked example, and it is EFX₀. -/
theorem example_ok : ∃ X, mrd exInst = some X ∧ exInst.EFX0 X := by
  have h : (mrd exInst).isSome = true := by decide
  cases hm : mrd exInst with
  | none => rw [hm] at h; simp at h
  | some X => exact ⟨X, rfl, mrd_sound exInst (twoRelCheck_sound exInst (by decide)) X hm⟩

def exInst2 : Inst where
  n := 4
  m := 4
  v := fun i g =>
    match i.val, g.val with
    | 0, 0 => 3 | 0, 1 => 1
    | 1, 0 => 3 | 1, 1 => 1
    | 2, 0 => 3 | 2, 1 => 1
    | 3, 2 => 4
    | _, _ => 0

theorem example2_ok : ∃ X, mrd exInst2 = some X ∧ exInst2.EFX0 X := by
  have h : (mrd exInst2).isSome = true := by decide
  cases hm : mrd exInst2 with
  | none => rw [hm] at h; simp at h
  | some X => exact ⟨X, rfl, mrd_sound exInst2 (twoRelCheck_sound exInst2 (by decide)) X hm⟩

end MRD

#print axioms MRD.PAssign.dump_efx0
#print axioms MRD.phase1_inv
#print axioms MRD.rotate_inv
#print axioms MRD.mrd_sound
#print axioms MRD.example_ok
#print axioms MRD.example2_ok
#print axioms MRD.mrd_total_of_unassigned
#print axioms MRD.mrd_total_all_assigned
#print axioms MRD.mrd_total
#print axioms MRD.rotate_totalU_lt
#print axioms MRD.mrdA_sound
#print axioms MRD.mrdA_eq
#print axioms MRD.lastAgent_source
#print axioms MRD.mrdG_efx0
#print axioms MRD.mrdGA_efx0
#print axioms MRD.twoRelevant_of_count
#print axioms MRD.exists_efx0_of_count
#print axioms MRD.efx0Check_iff
#print axioms MRD.mrdG_shape
#print axioms MRD.findCycle_phase1
#print axioms MRD.mrd_total_unconditional
#print axioms MRD.mrd_correct
#print axioms MRD.efx0_of_invariants
#print axioms MRD.main_theorem
