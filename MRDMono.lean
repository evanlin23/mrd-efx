import MRD
set_option autoImplicit false

/-!
# 2-relevant instances with general monotone valuations: a formal proof

Each agent `i` has two slots `a i, b i : Fin m` (equal if it cares about one good only) and a value
table `f i : Bool → Bool → Nat` giving the value of a bundle according to whether it contains `a i`
and whether it contains `b i`. Monotonicity: `f i false false = 0` and both singleton values are at
most the pair value. This covers additive, substitute and complementary preferences on the two
goods.

Algorithm: one greedy pass in index order — an agent takes its most valuable available slot among
the eligible ones (a slot is eligible if its singleton value is positive, or if the agent is
*complementary*, i.e. both singleton values are zero but the pair is worth something); then the
unassigned goods are dumped on an unassigned agent if there is one, else on the last agent.
-/

namespace MRDM
open MRD (findFin findFin_some findFin_none allFin allFin_true ifp ifn)

structure MInst where
  n : Nat
  m : Nat
  a : Fin n → Fin m
  b : Fin n → Fin m
  f : Fin n → Bool → Bool → Nat
  f00 : ∀ i, f i false false = 0
  mono_a : ∀ i, f i false true ≤ f i true true
  mono_b : ∀ i, f i true false ≤ f i true true

namespace MInst
variable (I : MInst)

abbrev Alloc := Fin I.m → Fin I.n

/-- Value of the singleton `{g}` for agent `i`. -/
def sv (i : Fin I.n) (g : Fin I.m) : Nat := I.f i (decide (g = I.a i)) (decide (g = I.b i))

/-- Whether good `g` lies in bundle `j` with `ex` removed. -/
def has (X : I.Alloc) (j : Fin I.n) (ex : Option (Fin I.m)) (g : Fin I.m) : Bool :=
  decide (X g = j ∧ ex ≠ some g)

/-- Value of bundle `j` to agent `i` with `ex` removed: the table entry for which of the two slots
are present. -/
def bundleVal (X : I.Alloc) (i j : Fin I.n) (ex : Option (Fin I.m)) : Nat :=
  I.f i (I.has X j ex (I.a i)) (I.has X j ex (I.b i))

/-- Strong EFX₀. -/
def EFX0 (X : I.Alloc) : Prop :=
  ∀ i j : Fin I.n, i ≠ j → ∀ g : Fin I.m, X g = j →
    I.bundleVal X i j (some g) ≤ I.bundleVal X i i none

/-- A good is relevant to `i` iff it is one of its two slots. -/
def Rel (i : Fin I.n) (g : Fin I.m) : Prop := g = I.a i ∨ g = I.b i

/-- Irrelevant goods have singleton value zero. -/
theorem sv_irrel (i : Fin I.n) (g : Fin I.m) (h : ¬ I.Rel i g) : I.sv i g = 0 := by
  unfold sv
  have ha : ¬ g = I.a i := fun e => h (Or.inl e)
  have hb : ¬ g = I.b i := fun e => h (Or.inr e)
  simp [ha, hb, I.f00]

theorem sv_a (i : Fin I.n) (hab : I.a i ≠ I.b i) : I.sv i (I.a i) = I.f i true false := by
  unfold sv; simp [hab]

theorem sv_b (i : Fin I.n) (hab : I.a i ≠ I.b i) : I.sv i (I.b i) = I.f i false true := by
  unfold sv; simp [Ne.symm hab]

theorem sv_ab (i : Fin I.n) (hab : I.a i = I.b i) : I.sv i (I.a i) = I.f i true true := by
  unfold sv; simp [hab]

/-- Complementary agent: worthless singletons, valuable pair. -/
def complB (i : Fin I.n) : Bool :=
  decide (I.a i ≠ I.b i) && decide (I.sv i (I.a i) = 0) && decide (I.sv i (I.b i) = 0) &&
    decide (0 < I.f i true true)

/-- A non-complementary agent with distinct, worthless singletons values the pair at zero. -/
theorem pair_zero_of_not_compl (i : Fin I.n) (hab : I.a i ≠ I.b i) (ha : I.sv i (I.a i) = 0)
    (hb : I.sv i (I.b i) = 0) (hc : I.complB i = false) : I.f i true true = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have ht : I.complB i = true := by unfold complB; simp [hab, ha, hb, hpos]
  rw [ht] at hc
  cases hc

end MInst

/-! ## Partial assignments and the dump step -/

/-- A partial injective assignment of relevant goods to agents: each agent holds at most one good,
which must be one of its slots, and no good is held twice. -/
structure PA (I : MInst) where
  ρ : Fin I.n → Option (Fin I.m)
  rel : ∀ i g, ρ i = some g → I.Rel i g
  inj : ∀ i j g, ρ i = some g → ρ j = some g → i = j

namespace PA
variable {I : MInst} (A : PA I)

def util (i : Fin I.n) : Nat :=
  match A.ρ i with
  | some g => I.sv i g
  | none => 0

theorem util_some (i : Fin I.n) (g : Fin I.m) (h : A.ρ i = some g) : A.util i = I.sv i g := by
  simp [util, h]
theorem util_none (i : Fin I.n) (h : A.ρ i = none) : A.util i = 0 := by
  simp [util, h]

def Unassigned (g : Fin I.m) : Prop := ∀ i, A.ρ i ≠ some g

def holder (g : Fin I.m) : Option (Fin I.n) := findFin I.n (fun i => decide (A.ρ i = some g))

theorem holder_some (g : Fin I.m) (j : Fin I.n) (h : A.holder g = some j) : A.ρ j = some g := by
  have := findFin_some _ _ _ h
  simpa using this

theorem holder_none (g : Fin I.m) (h : A.holder g = none) : A.Unassigned g := by
  intro i hi
  have := findFin_none _ _ h i
  simp at this
  exact this hi

/-- The dump: held goods stay with their holders; every unassigned good goes to the sink `s`. -/
def dump (s : Fin I.n) : I.Alloc := fun g =>
  match A.holder g with
  | some j => j
  | none => s

theorem dump_eq_iff (s j : Fin I.n) (hjs : j ≠ s) (g : Fin I.m) :
    A.dump s g = j ↔ A.ρ j = some g := by
  unfold dump
  cases hh : A.holder g with
  | some j' =>
    show j' = j ↔ _
    constructor
    · intro e; rw [← e]; exact A.holder_some g _ hh
    · intro hj; exact A.inj j' j g (A.holder_some g j' hh) hj
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

/-- (P1): every positively valued slot of an unassigned agent is held by somebody. -/
def P1 : Prop := ∀ i, A.ρ i = none → ∀ g, I.Rel i g → 0 < I.sv i g → ∃ j, A.ρ j = some g
/-- (P2): an assigned agent values its own good at least as much as any unassigned good. -/
def P2 : Prop := ∀ i g, A.ρ i = some g → ∀ g', A.Unassigned g' → I.sv i g' ≤ I.sv i g
/-- No unassigned agent has both goods free while valuing the pair positively. -/
def Cfix : Prop := ∀ i, A.ρ i = none → I.a i ≠ I.b i → A.Unassigned (I.a i) → A.Unassigned (I.b i) →
  I.f i true true = 0
/-- Nobody who does not hold `g` values it above their own good. -/
def Secure (g : Fin I.m) : Prop := ∀ i, A.ρ i ≠ some g → I.sv i g ≤ A.util i
/-- Unassigned agents find `g` ineligible: worthless as a singleton, and they are not complementary. -/
def SinkOK (g : Fin I.m) : Prop := ∀ i, A.ρ i = none → I.Rel i g → I.sv i g = 0 ∧ I.complB i = false

/-- Own bundle value for agents other than the sink. -/
theorem own_val (s i : Fin I.n) (his : i ≠ s) : I.bundleVal (A.dump s) i i none = A.util i := by
  unfold MInst.bundleVal MInst.has
  have key : ∀ g, decide (A.dump s g = i ∧ none ≠ some g) = decide (A.ρ i = some g) := by
    intro g
    rw [decide_eq_decide]
    constructor
    · intro h; exact (A.dump_eq_iff s i his g).mp h.1
    · intro h; exact ⟨(A.dump_eq_iff s i his g).mpr h, by simp⟩
  rw [key, key]
  cases hi : A.ρ i with
  | none => simp [I.f00, util, hi]
  | some h => simp [util, hi, MInst.sv]

/-- Removing a good from a singleton bundle leaves nothing. -/
theorem other_val (s i j : Fin I.n) (hjs : j ≠ s) (g : Fin I.m) (hg : A.dump s g = j) :
    I.bundleVal (A.dump s) i j (some g) = 0 := by
  unfold MInst.bundleVal MInst.has
  have hgj := (A.dump_eq_iff s j hjs g).mp hg
  have key : ∀ g', decide (A.dump s g' = j ∧ some g ≠ some g') = false := by
    intro g'
    apply decide_eq_false
    intro ⟨h1, h2⟩
    have := (A.dump_eq_iff s j hjs g').mp h1
    rw [hgj] at this
    exact h2 (by rw [Option.some.inj this])
  rw [key, key, I.f00]

/-- A relevant good sitting in the sink's bundle (other than the removed one) is not envied. -/
theorem sink_good (hP1 : A.P1) (hP2 : A.P2) (s : Fin I.n)
    (hs : A.ρ s = none ∨ ∃ g, A.ρ s = some g ∧ A.Secure g ∧ A.SinkOK g)
    (i : Fin I.n) (his : i ≠ s) (g' : Fin I.m) (hrel : I.Rel i g') (hin : A.dump s g' = s) :
    I.sv i g' ≤ A.util i := by
  rcases (A.dump_self_iff s g').mp hin with hsg | hun
  · rcases hs with hs0 | ⟨g0, hg0, hsec, _⟩
    · rw [hs0] at hsg; cases hsg
    · rw [hg0] at hsg
      cases hsg
      apply hsec i
      intro hi
      exact his (A.inj i s _ hi hg0)
  · cases hi : A.ρ i with
    | none =>
      rw [A.util_none i hi]
      apply Nat.le_of_not_lt
      intro hpos
      obtain ⟨j, hj⟩ := hP1 i hi g' hrel hpos
      exact hun j hj
    | some h =>
      rw [A.util_some i h hi]
      exact hP2 i h hi g' hun

/-- **The dump step is EFX₀** for general monotone two-good valuations. -/
theorem dump_efx0 (hP1 : A.P1) (hP2 : A.P2) (hC : A.Cfix) (s : Fin I.n)
    (hs : A.ρ s = none ∨ ∃ g, A.ρ s = some g ∧ A.Secure g ∧ A.SinkOK g) :
    I.EFX0 (A.dump s) := by
  intro i j hij g hg
  by_cases hjs : j = s
  · rw [hjs] at hij hg ⊢
    rw [A.own_val s i hij]
    -- the two membership bits of the sink's bundle minus g
    unfold MInst.bundleVal
    have hmem : ∀ g', I.has (A.dump s) s (some g) g' = true → A.dump s g' = s ∧ g ≠ g' := by
      intro g' h
      unfold MInst.has at h
      have := of_decide_eq_true h
      exact ⟨this.1, fun e => this.2 (by rw [e])⟩
    -- an agent that holds one of its slots does not see it in the sink's bundle
    have hnot : ∀ g', A.ρ i = some g' → I.has (A.dump s) s (some g) g' = false := by
      intro g' hg'
      apply decide_eq_false
      intro ⟨h1, _⟩
      have := (A.dump_self_iff s g').mp h1
      rcases this with hs' | hun
      · exact hij (A.inj i s g' hg' hs')
      · exact hun i hg'
    cases ha : I.has (A.dump s) s (some g) (I.a i) <;>
      cases hb : I.has (A.dump s) s (some g) (I.b i)
    · rw [I.f00]; exact Nat.zero_le _
    · -- only b is there
      by_cases hab : I.a i = I.b i
      · rw [hab] at ha; rw [ha] at hb; cases hb
      · rw [← I.sv_b i hab]
        exact A.sink_good hP1 hP2 s hs i hij (I.b i) (Or.inr rfl) (hmem _ hb).1
    · by_cases hab : I.a i = I.b i
      · rw [hab] at ha; rw [ha] at hb; cases hb
      · rw [← I.sv_a i hab]
        exact A.sink_good hP1 hP2 s hs i hij (I.a i) (Or.inl rfl) (hmem _ ha).1
    · -- both slots are in the sink's bundle minus g
      by_cases hab : I.a i = I.b i
      · rw [← I.sv_ab i hab]
        exact A.sink_good hP1 hP2 s hs i hij (I.a i) (Or.inl rfl) (hmem _ ha).1
      · -- i holds neither slot, hence nothing; both slots are unassigned, so the pair is worthless
        have hi : A.ρ i = none := by
          cases hi : A.ρ i with
          | none => rfl
          | some h =>
            rcases A.rel i h hi with e | e
            · rw [e] at hi; rw [hnot _ hi] at ha; cases ha
            · rw [e] at hi; rw [hnot _ hi] at hb; cases hb
        rw [A.util_none i hi]
        -- each slot in the sink's bundle is either the sink's own good or unassigned
        have hslot : ∀ g', I.has (A.dump s) s (some g) g' = true → A.ρ s = some g' ∨ A.Unassigned g' :=
          fun g' h => (A.dump_self_iff s g').mp (hmem _ h).1
        -- an unassigned slot is worthless to the unassigned agent `i`, by (P1)
        have hsv0 : ∀ g', I.Rel i g' → A.Unassigned g' → I.sv i g' = 0 := by
          intro g' hrel hun
          apply Nat.eq_zero_of_not_pos
          intro hpos
          obtain ⟨j, hj⟩ := hP1 i hi g' hrel hpos
          exact hun j hj
        -- a slot that is the sink's own good is ineligible for `i`, by `SinkOK`
        have hsink : ∀ g', I.Rel i g' → A.ρ s = some g' → I.sv i g' = 0 ∧ I.complB i = false := by
          intro g' hrel hsg
          rcases hs with hs0 | ⟨g0, hg0, _, hok⟩
          · rw [hs0] at hsg; cases hsg
          · rw [hg0] at hsg
            have e := Option.some.inj hsg
            subst e
            exact hok i hi hrel
        have hzero : I.f i true true = 0 := by
          rcases hslot (I.a i) ha with hsa | hua
          · rcases hslot (I.b i) hb with hsb | hub
            · exfalso
              rw [hsa] at hsb
              exact hab (Option.some.inj hsb)
            · obtain ⟨h1, hc⟩ := hsink (I.a i) (Or.inl rfl) hsa
              exact I.pair_zero_of_not_compl i hab h1 (hsv0 (I.b i) (Or.inr rfl) hub) hc
          · rcases hslot (I.b i) hb with hsb | hub
            · obtain ⟨h2, hc⟩ := hsink (I.b i) (Or.inr rfl) hsb
              exact I.pair_zero_of_not_compl i hab (hsv0 (I.a i) (Or.inl rfl) hua) h2 hc
            · exact hC i hi hab hua hub
        rw [hzero]
        exact Nat.le_refl _
  · rw [A.other_val s i j hjs g hg]
    exact Nat.zero_le _

end PA

/-! ## The greedy pass -/

section Exec
variable (I : MInst)

abbrev Rho := Fin I.n → Option (Fin I.m)

def freeB (ρ : Rho I) (g : Fin I.m) : Bool := (findFin I.n (fun i => decide (ρ i = some g))).isNone

theorem freeB_iff (ρ : Rho I) (g : Fin I.m) : freeB I ρ g = true ↔ ∀ i, ρ i ≠ some g := by
  unfold freeB
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

/-- Slot `g` of agent `i` is eligible: positive singleton value, or `i` is complementary. -/
def eligB (i : Fin I.n) (g : Fin I.m) : Bool := decide (0 < I.sv i g) || I.complB i

def assignTo (ρ : Rho I) (i : Fin I.n) (g : Fin I.m) : Rho I :=
  fun k => if k = i then some g else ρ k

/-- One greedy step: take the most valuable free eligible slot (slot `a` on ties). -/
def step (ρ : Rho I) (i : Fin I.n) : Rho I :=
  let ca := freeB I ρ (I.a i) && eligB I i (I.a i)
  let cb := freeB I ρ (I.b i) && eligB I i (I.b i)
  match ca, cb with
  | true, true =>
    if I.sv i (I.a i) < I.sv i (I.b i) then assignTo I ρ i (I.b i) else assignTo I ρ i (I.a i)
  | true, false => assignTo I ρ i (I.a i)
  | false, true => assignTo I ρ i (I.b i)
  | false, false => ρ

def phase1Upto : (t : Nat) → t ≤ I.n → Rho I
  | 0, _ => fun _ => none
  | t+1, h => step I (phase1Upto t (Nat.le_of_succ_le h)) ⟨t, h⟩

def phase1 : Rho I := phase1Upto I I.n (Nat.le_refl _)

/-- Invariants of the greedy pass after the first `t` agents have been processed. -/
structure InvUpto (t : Nat) (ρ : Rho I) : Prop where
  rel : ∀ i g, ρ i = some g → I.Rel i g
  inj : ∀ i j g, ρ i = some g → ρ j = some g → i = j
  p1 : ∀ i : Fin I.n, i.val < t → ρ i = none → ∀ g, I.Rel i g → 0 < I.sv i g → ∃ j, ρ j = some g
  p2 : ∀ i g, ρ i = some g → ∀ g', (∀ j, ρ j ≠ some g') → I.sv i g' ≤ I.sv i g
  cfix : ∀ i : Fin I.n, i.val < t → ρ i = none → I.a i ≠ I.b i → (∀ j, ρ j ≠ some (I.a i)) →
    (∀ j, ρ j ≠ some (I.b i)) → I.f i true true = 0
  unproc : ∀ i : Fin I.n, t ≤ i.val → ρ i = none
  later : ∀ i g, ρ i = some g → ∀ j g', ρ j = some g' → i.val < j.val → I.sv i g' ≤ I.sv i g
  /-- Every eligible slot of a processed-but-unassigned agent is held by an earlier-processed agent. -/
  holders : ∀ x : Fin I.n, x.val < t → ρ x = none → ∀ g, I.Rel x g → eligB I x g = true →
    ∃ y, ρ y = some g ∧ y.val < x.val

/-- What one step guarantees, stated once for both slots. -/
theorem step_facts (ρ : Rho I) (i : Fin I.n) (_hi : ρ i = none) :
    (step I ρ i = ρ ∧ (freeB I ρ (I.a i) && eligB I i (I.a i)) = false ∧
      (freeB I ρ (I.b i) && eligB I i (I.b i)) = false) ∨
    (∃ g, step I ρ i = assignTo I ρ i g ∧ I.Rel i g ∧ (∀ j, ρ j ≠ some g) ∧ eligB I i g = true ∧
      ∀ g', I.Rel i g' → (∀ j, ρ j ≠ some g') → eligB I i g' = true → I.sv i g' ≤ I.sv i g) := by
  unfold step
  simp only []
  cases hca : (freeB I ρ (I.a i) && eligB I i (I.a i)) <;>
    cases hcb : (freeB I ρ (I.b i) && eligB I i (I.b i))
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · -- only b
    simp only [Bool.and_eq_true] at hcb
    refine Or.inr ⟨I.b i, rfl, Or.inr rfl, (freeB_iff I ρ _).mp hcb.1, hcb.2, ?_⟩
    intro g' hrel hfree helig
    rcases hrel with e | e
    · subst e
      have : (freeB I ρ (I.a i) && eligB I i (I.a i)) = true := by
        rw [(freeB_iff I ρ _).mpr hfree, helig]; rfl
      rw [this] at hca; cases hca
    · subst e; exact Nat.le_refl _
  · simp only [Bool.and_eq_true] at hca
    refine Or.inr ⟨I.a i, rfl, Or.inl rfl, (freeB_iff I ρ _).mp hca.1, hca.2, ?_⟩
    intro g' hrel hfree helig
    rcases hrel with e | e
    · subst e; exact Nat.le_refl _
    · subst e
      have : (freeB I ρ (I.b i) && eligB I i (I.b i)) = true := by
        rw [(freeB_iff I ρ _).mpr hfree, helig]; rfl
      rw [this] at hcb; cases hcb
  · simp only [Bool.and_eq_true] at hca hcb
    by_cases hlt : I.sv i (I.a i) < I.sv i (I.b i)
    · rw [ifp hlt]
      refine Or.inr ⟨I.b i, rfl, Or.inr rfl, (freeB_iff I ρ _).mp hcb.1, hcb.2, ?_⟩
      intro g' hrel _ _
      rcases hrel with e | e
      · subst e; exact Nat.le_of_lt hlt
      · subst e; exact Nat.le_refl _
    · rw [ifn hlt]
      refine Or.inr ⟨I.a i, rfl, Or.inl rfl, (freeB_iff I ρ _).mp hca.1, hca.2, ?_⟩
      intro g' hrel _ _
      rcases hrel with e | e
      · subst e; exact Nat.le_refl _
      · subst e; exact Nat.le_of_not_lt hlt

/-- Eligibility of a free relevant good with positive value. -/
theorem elig_of_pos (i : Fin I.n) (g : Fin I.m) (h : 0 < I.sv i g) : eligB I i g = true := by
  unfold eligB; simp [h]

/-- An ineligible slot is worthless as a singleton, and its agent is not complementary. -/
theorem elig_false (i : Fin I.n) (g : Fin I.m) (h : eligB I i g = false) :
    I.sv i g = 0 ∧ I.complB i = false := by
  unfold eligB at h
  cases h1 : decide (0 < I.sv i g) with
  | true => rw [h1] at h; cases h
  | false =>
    cases h2 : I.complB i with
    | true => rw [h1, h2] at h; cases h
    | false => exact ⟨Nat.eq_zero_of_not_pos (of_decide_eq_false h1), rfl⟩

theorem step_inv (t : Nat) (ρ : Rho I) (hρ : InvUpto I t ρ) (i : Fin I.n) (hi : i.val = t) :
    InvUpto I (t+1) (step I ρ i) := by
  have hnone : ρ i = none := hρ.unproc i (by omega)
  rcases step_facts I ρ i hnone with ⟨heq, hca, hcb⟩ | ⟨g, heq, hrel, hfree, helig, hbest⟩
  · rw [heq]
    -- nothing was assigned: i's eligible slots were all taken
    have hnotfree : ∀ g, I.Rel i g → eligB I i g = true → ∃ j, ρ j = some g := by
      intro g hg he
      apply Classical.byContradiction
      intro hne
      have hf : freeB I ρ g = true := (freeB_iff I ρ g).mpr (fun j hj => hne ⟨j, hj⟩)
      rcases hg with e | e
      · subst e; rw [hf, he] at hca; cases hca
      · subst e; rw [hf, he] at hcb; cases hcb
    refine ⟨hρ.rel, hρ.inj, ?_, hρ.p2, ?_, ?_, hρ.later, ?_⟩
    · intro i' hlt h0 g hg hpos
      by_cases e : i'.val = t
      · have e' : i' = i := Fin.ext (by omega)
        subst e'
        exact hnotfree g hg (elig_of_pos I i' g hpos)
      · exact hρ.p1 i' (by omega) h0 g hg hpos
    · intro i' hlt h0 hab hua hub
      by_cases e : i'.val = t
      · have e' : i' = i := Fin.ext (by omega)
        subst e'
        apply Classical.byContradiction
        intro hne
        have hpos : 0 < I.f i' true true := Nat.pos_of_ne_zero hne
        -- either some singleton is positive (then eligible, then held: contradiction)
        -- or complementary
        by_cases hpa : 0 < I.sv i' (I.a i')
        · obtain ⟨j, hj⟩ := hnotfree (I.a i') (Or.inl rfl) (elig_of_pos I i' _ hpa)
          exact hua j hj
        · by_cases hpb : 0 < I.sv i' (I.b i')
          · obtain ⟨j, hj⟩ := hnotfree (I.b i') (Or.inr rfl) (elig_of_pos I i' _ hpb)
            exact hub j hj
          · have hc : I.complB i' = true := by
              unfold MInst.complB
              simp [hab, Nat.eq_zero_of_not_pos hpa, Nat.eq_zero_of_not_pos hpb, hpos]
            have he : eligB I i' (I.a i') = true := by unfold eligB; simp [hc]
            obtain ⟨j, hj⟩ := hnotfree (I.a i') (Or.inl rfl) he
            exact hua j hj
      · exact hρ.cfix i' (by omega) h0 hab hua hub
    · intro i' hle
      exact hρ.unproc i' (by omega)
    · intro x hlt h0 g hg he
      by_cases e : x.val = t
      · have e' : x = i := Fin.ext (by omega)
        subst e'
        obtain ⟨y', hy'⟩ := hnotfree g hg he
        refine ⟨y', hy', ?_⟩
        apply Classical.byContradiction
        intro hge
        have := hρ.unproc y' (Nat.le_of_not_lt (fun h => hge (by omega)))
        rw [this] at hy'; cases hy'
      · exact hρ.holders x (by omega) h0 g hg he
  · rw [heq]
    show InvUpto I (t+1) (fun k => if k = i then some g else ρ k)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k g' hk
      change (if k = i then some g else ρ k) = some g' at hk
      by_cases e : k = i
      · rw [ifp e] at hk; cases hk; rw [e]; exact hrel
      · rw [ifn e] at hk; exact hρ.rel k g' hk
    · intro k k' g' hk hk'
      change (if k = i then some g else ρ k) = some g' at hk
      change (if k' = i then some g else ρ k') = some g' at hk'
      by_cases e : k = i
      · by_cases e' : k' = i
        · rw [e, e']
        · rw [ifp e] at hk; rw [ifn e'] at hk'; cases hk; exact absurd hk' (hfree k')
      · by_cases e' : k' = i
        · rw [ifn e] at hk; rw [ifp e'] at hk'; cases hk'; exact absurd hk (hfree k)
        · rw [ifn e] at hk; rw [ifn e'] at hk'; exact hρ.inj k k' g' hk hk'
    · intro i' hlt h0 g' hg' hpos
      change (if i' = i then some g else ρ i') = none at h0
      by_cases e : i' = i
      · rw [ifp e] at h0; cases h0
      · rw [ifn e] at h0
        have hlt' : i'.val < t := by
          have : i'.val ≠ t := fun ee => e (Fin.ext (by omega))
          omega
        obtain ⟨j, hj⟩ := hρ.p1 i' hlt' h0 g' hg' hpos
        have hj' : j ≠ i := by intro ee; rw [ee, hnone] at hj; cases hj
        exact ⟨j, by show (if j = i then some g else ρ j) = some g'; rw [ifn hj']; exact hj⟩
    · intro k g0 hk g' hun
      change (if k = i then some g else ρ k) = some g0 at hk
      have hunρ : ∀ j, ρ j ≠ some g' := by
        intro j hj
        by_cases e : j = i
        · rw [e, hnone] at hj; cases hj
        · exact hun j (by show (if j = i then some g else ρ j) = some g'; rw [ifn e]; exact hj)
      by_cases e : k = i
      · rw [ifp e] at hk; cases hk; rw [e]
        by_cases hrel' : I.Rel i g'
        · by_cases hpos : 0 < I.sv i g'
          · exact hbest g' hrel' hunρ (elig_of_pos I i g' hpos)
          · rw [Nat.eq_zero_of_not_pos hpos]; exact Nat.zero_le _
        · rw [I.sv_irrel i g' hrel']; exact Nat.zero_le _
      · rw [ifn e] at hk; exact hρ.p2 k g0 hk g' hunρ
    · intro i' hlt h0 hab hua hub
      change (if i' = i then some g else ρ i') = none at h0
      by_cases e : i' = i
      · rw [ifp e] at h0; cases h0
      · rw [ifn e] at h0
        have hlt' : i'.val < t := by
          have : i'.val ≠ t := fun ee => e (Fin.ext (by omega))
          omega
        apply hρ.cfix i' hlt' h0 hab
        · intro j hj
          have hj' : j ≠ i := by intro ee; rw [ee, hnone] at hj; cases hj
          exact hua j
            (by show (if j = i then some g else ρ j) = some (I.a i'); rw [ifn hj']; exact hj)
        · intro j hj
          have hj' : j ≠ i := by intro ee; rw [ee, hnone] at hj; cases hj
          exact hub j
            (by show (if j = i then some g else ρ j) = some (I.b i'); rw [ifn hj']; exact hj)
    · intro k hle
      have e : k ≠ i := by intro ee; rw [ee] at hle; omega
      show (if k = i then some g else ρ k) = none
      rw [ifn e]; exact hρ.unproc k (by omega)
    · intro k g0 hk j g' hj hlt
      change (if k = i then some g else ρ k) = some g0 at hk
      change (if j = i then some g else ρ j) = some g' at hj
      by_cases ej : j = i
      · rw [ifp ej] at hj; cases hj
        have ek : k ≠ i := fun e => by rw [e, ej] at hlt; exact Nat.lt_irrefl _ hlt
        rw [ifn ek] at hk
        exact hρ.p2 k g0 hk g hfree
      · rw [ifn ej] at hj
        by_cases ek : k = i
        · rw [ek, hi] at hlt
          have hj0 := hρ.unproc j (by omega)
          rw [hj0] at hj; cases hj
        · rw [ifn ek] at hk; exact hρ.later k g0 hk j g' hj hlt
    · intro x hlt h0 g' hg' he
      change (if x = i then some g else ρ x) = none at h0
      by_cases e : x = i
      · rw [ifp e] at h0; cases h0
      · rw [ifn e] at h0
        have hlt' : x.val < t := by
          have : x.val ≠ t := fun ee => e (Fin.ext (by omega))
          omega
        obtain ⟨y, hy, hyx⟩ := hρ.holders x hlt' h0 g' hg' he
        have hyi : y ≠ i := by intro ee; rw [ee, hnone] at hy; cases hy
        exact ⟨y, by show (if y = i then some g else ρ y) = some g'; rw [ifn hyi]; exact hy, hyx⟩

theorem phase1Upto_inv : ∀ (t : Nat) (h : t ≤ I.n), InvUpto I t (phase1Upto I t h)
  | 0, _ =>
    ⟨fun _ _ hk => by simp [phase1Upto] at hk, fun _ _ _ hk => by simp [phase1Upto] at hk,
     fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ _ hk => by simp [phase1Upto] at hk,
     fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl,
     fun _ _ hk => by simp [phase1Upto] at hk,
     fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | t+1, h => step_inv I t _ (phase1Upto_inv t (Nat.le_of_succ_le h)) ⟨t, h⟩ rfl

def toPA (ρ : Rho I) (h : InvUpto I I.n ρ) : PA I := ⟨ρ, h.rel, h.inj⟩

def firstUnassigned (ρ : Rho I) : Option (Fin I.n) := findFin I.n (fun i => decide (ρ i = none))
def lastAgent (hn : 0 < I.n) : Fin I.n := ⟨I.n - 1, Nat.sub_lt hn Nat.one_pos⟩

def dumpE (ρ : Rho I) (s : Fin I.n) : I.Alloc := fun g =>
  match findFin I.n (fun i => decide (ρ i = some g)) with
  | some j => j
  | none => s

/-- The algorithm. -/
def mrdM (hn : 0 < I.n) : I.Alloc :=
  match firstUnassigned I (phase1 I) with
  | some s => dumpE I (phase1 I) s
  | none => dumpE I (phase1 I) (lastAgent I hn)

theorem dumpE_eq (ρ : Rho I) (h : InvUpto I I.n ρ) (s : Fin I.n) :
    dumpE I ρ s = (toPA I ρ h).dump s := rfl

/-- **End-to-end theorem for general monotone two-good valuations.** -/
theorem mrdM_efx0 (hn : 0 < I.n) : I.EFX0 (mrdM I hn) := by
  have hinv : InvUpto I I.n (phase1 I) := phase1Upto_inv I I.n (Nat.le_refl _)
  have hP1 : (toPA I _ hinv).P1 := fun i hi g hg hp => hinv.p1 i i.isLt hi g hg hp
  have hP2 : (toPA I _ hinv).P2 := hinv.p2
  have hC : (toPA I _ hinv).Cfix := fun i hi hab hua hub => hinv.cfix i i.isLt hi hab hua hub
  unfold mrdM
  cases hf : firstUnassigned I (phase1 I) with
  | some s =>
    show I.EFX0 (dumpE I (phase1 I) s)
    have hs : phase1 I s = none := by have := findFin_some _ _ _ hf; simpa using this
    rw [dumpE_eq I _ hinv s]
    exact (toPA I _ hinv).dump_efx0 hP1 hP2 hC s (Or.inl hs)
  | none =>
    show I.EFX0 (dumpE I (phase1 I) (lastAgent I hn))
    have hall : ∀ i, phase1 I i ≠ none := by
      intro i hi; have := findFin_none _ _ hf i; simp at this; exact this hi
    rw [dumpE_eq I _ hinv (lastAgent I hn)]
    apply (toPA I _ hinv).dump_efx0 hP1 hP2 hC (lastAgent I hn)
    apply Or.inr
    cases hL : phase1 I (lastAgent I hn) with
    | none => exact absurd hL (hall _)
    | some g =>
      refine ⟨g, hL, ?_, fun i hi => absurd hi (hall i)⟩
      intro i hi
      cases hi' : phase1 I i with
      | none => exact absurd hi' (hall i)
      | some g0 =>
        rw [(toPA I _ hinv).util_some i g0 hi']
        by_cases e : i = lastAgent I hn
        · have hh : (toPA I (phase1 I) hinv).ρ i = some g := by
            show phase1 I i = some g
            rw [e]; exact hL
          exact absurd hh hi
        · have hlt : i.val < (lastAgent I hn).val := by
            have h1 : i.val ≠ I.n - 1 := fun h => e (Fin.ext h)
            have h2 := i.isLt
            show i.val < I.n - 1
            omega
          exact hinv.later i g0 hi' (lastAgent I hn) g hL hlt

/-- **The simplest form of the algorithm**: greedy Phase 1, then every unassigned good goes to the
agent processed last, whether or not that agent holds a good. -/
def mrdML (hn : 0 < I.n) : I.Alloc := dumpE I (phase1 I) (lastAgent I hn)

theorem mrdML_efx0 (hn : 0 < I.n) : I.EFX0 (mrdML I hn) := by
  have hinv : InvUpto I I.n (phase1 I) := phase1Upto_inv I I.n (Nat.le_refl _)
  have hP1 : (toPA I _ hinv).P1 := fun i hi g hg hp => hinv.p1 i i.isLt hi g hg hp
  have hP2 : (toPA I _ hinv).P2 := hinv.p2
  have hC : (toPA I _ hinv).Cfix := fun i hi hab hua hub => hinv.cfix i i.isLt hi hab hua hub
  unfold mrdML
  rw [dumpE_eq I _ hinv (lastAgent I hn)]
  apply (toPA I _ hinv).dump_efx0 hP1 hP2 hC (lastAgent I hn)
  cases hL : phase1 I (lastAgent I hn) with
  | none => exact Or.inl hL
  | some g =>
    -- an unassigned agent finds `g` ineligible: otherwise its holder, the last agent, would have
    -- been processed earlier
    have hinel : ∀ i, phase1 I i = none → I.Rel i g → eligB I i g = false := by
      intro i hi hrel
      cases he : eligB I i g with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨y, hy, hlt⟩ := hinv.holders i i.isLt hi g hrel he
        have hyl : y = lastAgent I hn := hinv.inj y (lastAgent I hn) g hy hL
        rw [hyl] at hlt
        have h1 := i.isLt
        have h2 : (lastAgent I hn).val = I.n - 1 := rfl
        omega
    refine Or.inr ⟨g, hL, ?_, ?_⟩
    · intro i hi
      cases hi' : phase1 I i with
      | none =>
        rw [(toPA I _ hinv).util_none i hi']
        by_cases hrel : I.Rel i g
        · rw [(elig_false I i g (hinel i hi' hrel)).1]
          exact Nat.le_refl _
        · rw [I.sv_irrel i g hrel]
          exact Nat.le_refl _
      | some g0 =>
        rw [(toPA I _ hinv).util_some i g0 hi']
        by_cases e : i = lastAgent I hn
        · have hh : (toPA I (phase1 I) hinv).ρ i = some g := by
            show phase1 I i = some g
            rw [e]; exact hL
          exact absurd hh hi
        · have hlt : i.val < (lastAgent I hn).val := by
            have h1 : i.val ≠ I.n - 1 := fun h => e (Fin.ext h)
            have h2 := i.isLt
            show i.val < I.n - 1
            omega
          exact hinv.later i g0 hi' (lastAgent I hn) g hL hlt
    · intro i hi hrel
      exact elig_false I i g (hinel i hi hrel)

end Exec

/-! ## A sound checker and a kernel-checked example with a complementary agent -/

namespace MInst
variable (I : MInst)

/-- Boolean checker for strong EFX₀ in the monotone model. -/
def efx0Check (X : I.Alloc) : Bool :=
  allFin I.n fun i => allFin I.n fun j =>
    if i = j then true else
    allFin I.m fun g =>
      if X g = j then decide (I.bundleVal X i j (some g) ≤ I.bundleVal X i i none) else true

/-- Soundness of the checker: `true` implies strong EFX₀. -/
theorem efx0Check_sound (X : I.Alloc) (h : I.efx0Check X = true) : I.EFX0 X := by
  intro i j hij g hg
  have h1 := allFin_true _ _ h i
  have h2 := allFin_true _ _ h1 j
  rw [ifn hij] at h2
  have h3 := allFin_true _ _ h2 g
  rw [ifp hg] at h3
  exact of_decide_eq_true h3

end MInst

/-- Three agents, five goods. Agent 0: goods 0,1 are substitutes (3, 1, pair 3). Agent 1: goods 1,2
are complements (0, 0, pair 5). Agent 2: goods 2,3 additive (2, 4, pair 6). Good 4 is worthless. -/
def exM : MInst where
  n := 3
  m := 5
  a := fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | _ => ⟨2, by decide⟩
  b := fun i => match i.val with | 0 => ⟨1, by decide⟩ | 1 => ⟨2, by decide⟩ | _ => ⟨3, by decide⟩
  f := fun i ha hb =>
    match i.val, ha, hb with
    | 0, true, false => 3 | 0, false, true => 1 | 0, true, true => 3
    | 1, true, true => 5
    | 2, true, false => 2 | 2, false, true => 4 | 2, true, true => 6
    | _, _, _ => 0
  f00 := by intro i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
  mono_a := by
    intro i
    match i with
    | ⟨0, _⟩ => decide +revert
    | ⟨1, _⟩ => decide +revert
    | ⟨2, _⟩ => decide +revert
  mono_b := by
    intro i
    match i with
    | ⟨0, _⟩ => decide +revert
    | ⟨1, _⟩ => decide +revert
    | ⟨2, _⟩ => decide +revert

/-- The algorithm's output on `exM` is strongly EFX₀, kernel-checked through the sound checker. -/
theorem exM_ok : exM.EFX0 (mrdM exM (by decide)) := MInst.efx0Check_sound _ _ (by decide)

/-- The allocation computed on `exM`, good by good: goods `0` and `1` go to agents `0` and `1`, and
goods `2`, `3`, `4` to agent `2` (kernel-checked). -/
theorem exM_alloc :
    (List.range 5).map (fun g => (mrdM exM (by decide) ⟨g % 5, Nat.mod_lt _ (by decide)⟩).val)
      = [0, 1, 2, 2, 2] := by
  decide

/-! ## Shape and existence, as in the additive development -/

section Shape
variable (I : MInst)

/-- Every bundle other than the sink's contains at most one good. -/
theorem dump_thin_other (A : PA I) (s j : Fin I.n) (hjs : j ≠ s) (g g' : Fin I.m)
    (hg : A.dump s g = j) (hg' : A.dump s g' = j) : g = g' := by
  have e1 := (A.dump_eq_iff s j hjs g).mp hg
  have e2 := (A.dump_eq_iff s j hjs g').mp hg'
  rw [e1] at e2
  exact Option.some.inj e2

/-- All bundles but one contain at most one good. -/
theorem mrdM_shape (hn : 0 < I.n) :
    ∃ s, ∀ j, j ≠ s → ∀ g g', mrdM I hn g = j → mrdM I hn g' = j → g = g' := by
  have hinv : InvUpto I I.n (phase1 I) := phase1Upto_inv I I.n (Nat.le_refl _)
  unfold mrdM
  cases hf : firstUnassigned I (phase1 I) with
  | some s =>
    show ∃ s', ∀ j, j ≠ s' → ∀ g g',
      dumpE I (phase1 I) s g = j → dumpE I (phase1 I) s g' = j → g = g'
    refine ⟨s, fun j hjs g g' hg hg' => ?_⟩
    rw [dumpE_eq I _ hinv s] at hg hg'
    exact dump_thin_other I _ s j hjs g g' hg hg'
  | none =>
    show ∃ s', ∀ j, j ≠ s' → ∀ g g', dumpE I (phase1 I) (lastAgent I hn) g = j →
      dumpE I (phase1 I) (lastAgent I hn) g' = j → g = g'
    refine ⟨lastAgent I hn, fun j hjs g g' hg hg' => ?_⟩
    rw [dumpE_eq I _ hinv (lastAgent I hn)] at hg hg'
    exact dump_thin_other I _ (lastAgent I hn) j hjs g g' hg hg'

/-- **Headline theorem, monotone version**: existence of a complete strongly-EFX₀ allocation in
which all bundles but one contain at most one good, for arbitrary monotone valuations on at most two
goods. -/
theorem main_theorem (hn : 0 < I.n) :
    ∃ X : I.Alloc, I.EFX0 X ∧ ∃ s, ∀ j, j ≠ s → ∀ g g', X g = j → X g' = j → g = g' :=
  ⟨mrdM I hn, mrdM_efx0 I hn, mrdM_shape I hn⟩

theorem mrdML_shape (hn : 0 < I.n) :
    ∃ s, ∀ j, j ≠ s → ∀ g g', mrdML I hn g = j → mrdML I hn g' = j → g = g' := by
  have hinv : InvUpto I I.n (phase1 I) := phase1Upto_inv I I.n (Nat.le_refl _)
  unfold mrdML
  refine ⟨lastAgent I hn, fun j hjs g g' hg hg' => ?_⟩
  rw [dumpE_eq I _ hinv (lastAgent I hn)] at hg hg'
  exact dump_thin_other I _ (lastAgent I hn) j hjs g g' hg hg'

/-- **Headline theorem, simplest algorithm, monotone version.** -/
theorem main_theorem_L (hn : 0 < I.n) :
    ∃ X : I.Alloc, I.EFX0 X ∧ ∃ s, ∀ j, j ≠ s → ∀ g g', X g = j → X g' = j → g = g' :=
  ⟨mrdML I hn, mrdML_efx0 I hn, mrdML_shape I hn⟩

end Shape

end MRDM

#print axioms MRDM.PA.dump_efx0
#print axioms MRDM.mrdM_efx0
#print axioms MRDM.exM_ok
#print axioms MRDM.main_theorem
#print axioms MRDM.mrdML_efx0
#print axioms MRDM.main_theorem_L
