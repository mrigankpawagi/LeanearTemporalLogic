import Mathlib
import LeanearTemporalLogic.Worlds
import LeanearTemporalLogic.LTL
import LeanearTemporalLogic.Satisfaction

/-!
## Satisfaction of LTL Formulae

Defines the recursive satisfaction relation for LTL formulae by worlds, and provides instances for worlds and states.
-/
open LTLFormula

/--
Satisfaction of LTL formulae by worlds.
-/
def world_satisfies_ltl {AP: Type} (σ : World AP) : LTLFormula AP → Prop
  | ⊤ => true
  | LTLFormula.atom a => a ∈ σ 0
  | ¬ ψ => ¬ (world_satisfies_ltl σ ψ)
  | ϕ₁ ∧ ϕ₂ => (world_satisfies_ltl σ ϕ₁) ∧ (world_satisfies_ltl σ ϕ₂)
  | ◯ ψ => world_satisfies_ltl (σ[1…]) ψ
  | ϕ₁ 𝓤 ϕ₂ => ∃ (j: ℕ), ((world_satisfies_ltl (σ[j…]) ϕ₂) ∧ ∀ (k: ℕ), (k < j → world_satisfies_ltl (σ[k…]) ϕ₁))

instance {AP: Type} : Satisfaction (World AP) (LTLFormula AP) := ⟨world_satisfies_ltl⟩

/--
Satisfaction of an LTL formula by a set of atomic propositions is defined as the satisfaction of the formula by a world that starts with that set and subsequently has empty sets.
-/
instance {AP: Type} : Satisfaction (Set AP) (LTLFormula AP) := ⟨fun A ϕ => by
  let f : World AP := fun n => if n = 0 then A else ∅
  exact f ⊨ ϕ⟩

/-!
## Useful Lemmas for Satisfaction

These lemmas provide convenient equivalences for satisfaction of various logical and temporal operators.
-/
/--
Satisfaction of negation: `(σ ⊨ (¬ ϕ)) ↔ (¬ (σ ⊨ ϕ))`.
-/
theorem world_satisfies_not {AP: Type} (σ : World AP) (ϕ : LTLFormula AP) : (σ ⊨ (¬ ϕ)) ↔ (¬ (σ ⊨ ϕ)) := by
  simp only [Satisfaction.Satisfies]
  rfl

/--
Satisfaction of conjunction: `(σ ⊨ (ϕ₁ ∧ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∧ (σ ⊨ ϕ₂))`.
-/
theorem world_satisfies_and {AP: Type} (σ : World AP) (ϕ₁ ϕ₂ : LTLFormula AP) : (σ ⊨ (ϕ₁ ∧ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∧ (σ ⊨ ϕ₂)) := by
  simp only [Satisfaction.Satisfies]
  rfl

/--
Satisfaction of disjunction: `(σ ⊨ (ϕ₁ ∨ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∨ (σ ⊨ ϕ₂))`.
-/
def world_satisfies_or {AP: Type} (σ : World AP) (ϕ₁ ϕ₂ : LTLFormula AP) : (σ ⊨ (ϕ₁ ∨ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∨ (σ ⊨ ϕ₂)) := by
  rw [or_def, world_satisfies_not, world_satisfies_and, world_satisfies_not, world_satisfies_not]
  simp only [Not.not, And.and]
  rw [not_and, not_not, ← or_iff_not_imp_left]
  rfl

/--
Satisfaction of next: `(σ ⊨ (◯ ϕ)) ↔ ((σ[1…]) ⊨ ϕ)`.
-/
theorem world_satisfies_next {AP: Type} (σ : World AP) (ϕ : LTLFormula AP) : (σ ⊨ (◯ ϕ)) ↔ ((σ[1…]) ⊨ ϕ) := by
  simp only [Satisfaction.Satisfies]
  rw [world_satisfies_ltl]

/--
Satisfaction of until: `(σ ⊨ (ϕ₁ 𝓤 ϕ₂)) ↔ ∃ (j: ℕ), (((σ[j…]) ⊨ ϕ₂) ∧ ∀ (k: ℕ), (k < j → ((σ[k…]) ⊨ ϕ₁)))`.
-/
theorem world_satisfies_until {AP: Type} (σ : World AP) (ϕ₁ ϕ₂ : LTLFormula AP) : (σ ⊨ (ϕ₁ 𝓤 ϕ₂)) ↔ ∃ (j: ℕ), (((σ[j…]) ⊨ ϕ₂) ∧ ∀ (k: ℕ), (k < j → ((σ[k…]) ⊨ ϕ₁))) := by
  simp only [Satisfaction.Satisfies]
  rw [world_satisfies_ltl]

/-!
## Eventually and Always

Lemmas for satisfaction of the derived temporal operators "eventually" and "always", and their compositions.
-/
/--
Satisfaction of eventually: `(σ ⊨ (♢ ϕ)) ↔ ∃ (i: ℕ), ((σ[i…]) ⊨ ϕ)`.
-/
theorem world_satisfies_eventually {AP: Type} (σ : World AP) (ϕ : LTLFormula AP) : (σ ⊨ (♢ ϕ)) ↔ ∃ (i: ℕ), ((σ[i…]) ⊨ ϕ) := by
  unfold eventually
  simp only [Satisfaction.Satisfies]
  rw [world_satisfies_ltl]

  constructor
  -- left to right
  · intro h
    obtain ⟨i, hi⟩ := h
    obtain ⟨hl, hr⟩ := hi
    use i

  -- right to left
  · intro h
    obtain ⟨i, hi⟩ := h
    use i
    constructor
    · assumption
    · intro k
      intro hk
      rw [world_satisfies_ltl]

/--
Satisfaction of always: `(σ ⊨ (□ ϕ)) ↔ ∀ (i: ℕ), ((σ[i…]) ⊨ ϕ)`.
-/
theorem world_satisfies_always {AP: Type} (σ : World AP) (ϕ : LTLFormula AP) : (σ ⊨ (□ ϕ)) ↔ ∀ (i: ℕ), ((σ[i…]) ⊨ ϕ) := by
  rw [always_def, world_satisfies_not, world_satisfies_eventually]
  simp only [world_satisfies_not]
  simp [Not.not]

/--
Satisfaction of always eventually: `(σ ⊨ (□ ♢ ϕ)) ↔ ∀ (i: ℕ), ∃ (j: ℕ), ((σ[i+j…]) ⊨ ϕ)`.
-/
theorem world_satisfies_always_eventually {AP: Type} (σ : World AP) (ϕ : LTLFormula AP) : (σ ⊨ (□ ♢ ϕ)) ↔ ∀ (i: ℕ), ∃ (j: ℕ), ((σ[i+j…]) ⊨ ϕ) := by
  constructor

  -- left to right
  · intro h
    intro i
    rw [world_satisfies_always] at h
    specialize h i
    rw [world_satisfies_eventually] at h
    obtain ⟨j, hj⟩ := h
    rw [Suffix.composition] at hj
    use j

  -- right to left
  · intro h
    rw [world_satisfies_always]
    intro i
    rw [world_satisfies_eventually]
    specialize h i
    obtain ⟨j, hj⟩ := h
    use j
    rw [Suffix.composition]
    assumption

/--
Satisfaction of eventually always: `(σ ⊨ (♢ □ ϕ)) ↔ ∃ (i: ℕ), ∀ (j: ℕ), ((σ[i+j…]) ⊨ ϕ)`.
-/
theorem world_satisfies_eventually_always {AP: Type} (σ : World AP) (ϕ : LTLFormula AP) : (σ ⊨ (♢ □ ϕ)) ↔ ∃ (i: ℕ), ∀ (j: ℕ), ((σ[i+j…]) ⊨ ϕ) := by
  constructor

  -- left to right
  · intro h
    rw [world_satisfies_eventually] at h
    obtain ⟨i, hi⟩ := h
    use i
    intro j
    rw [world_satisfies_always] at hi
    specialize hi j
    rw [Suffix.composition] at hi
    assumption

  -- right to left
  · intro h
    rw [world_satisfies_eventually]
    obtain ⟨i, hi⟩ := h
    use i
    rw [world_satisfies_always]
    intro j
    specialize hi j
    rw [Suffix.composition]
    assumption

/--
Satisfaction of weak until: `(σ ⊨ (ϕ₁ 𝓦 ϕ₂)) ↔ ((σ ⊨ (ϕ₁ 𝓤 ϕ₂)) ∨ (σ ⊨ (□ ϕ₁)))`.
-/
theorem world_satisfies_weakuntil {AP: Type} (σ : World AP) (ϕ₁ ϕ₂ : LTLFormula AP) : (σ ⊨ (ϕ₁ 𝓦 ϕ₂)) ↔ ((σ ⊨ (ϕ₁ 𝓤 ϕ₂)) ∨ (σ ⊨ (□ ϕ₁))) := by
  rw [weakuntil]
  rw [world_satisfies_or]

/--
If a world satisfies an LTL formula, it satisfies it for the first time at some index.
-/
theorem satisfies_for_first_time_iff_satisfies {AP: Type} (ϕ : LTLFormula AP) (σ : World AP) (h: ∃ (x : ℕ), Suffix σ x ⊨ ϕ) : ∃ x, (Suffix σ x ⊨ ϕ) ∧ (∀ y < x, ¬ (Suffix σ y ⊨ ϕ)) := by
  by_contra hc
  simp only [And.and, not_exists, not_and, not_forall, Classical.not_imp] at hc
  have h'' (x : ℕ): ∀ k ≤ x, Suffix σ k ⊨ (¬ ϕ) := by
    induction x with
    | zero =>
      intro k hk
      simp only [nonpos_iff_eq_zero] at hk
      rw [hk]
      specialize hc 0
      simp only [not_lt_zero', IsEmpty.exists_iff, exists_const, imp_false] at hc
      assumption
    | succ n ih =>
      intro k hk
      by_contra hc'
      specialize hc k
      rw [world_satisfies_not] at hc'
      simp only [Not.not, not_not] at hc hc' hc'
      apply hc at hc'
      obtain ⟨i, hi, hc'⟩ := hc'
      have hi' : i ≤ n := by
        rw [Nat.lt_iff_add_one_le] at hi
        have hi'' : i + 1 ≤ n + 1 := Nat.le_trans hi hk
        rw [Nat.add_le_add_iff_right] at hi''
        assumption

      specialize ih i hi'
      contradiction

  have h''' (x : ℕ) : Suffix σ x ⊨ (¬ ϕ) := by
    specialize h'' x x (by simp only [le_refl])
    assumption

  obtain ⟨i, hi⟩ := h
  specialize h''' i
  contradiction

/-!
## Worlds Satisfying an LTL Formula

The set of all worlds that satisfy a given LTL formula.
-/
def Worlds {AP: Type} (ϕ : LTLFormula AP) : Set (World AP) := fun σ => σ ⊨ ϕ

/-!
## Equivalence of LTL Formulae

Two LTL formulae are equivalent if their worlds coincide.
-/
instance {AP: Type} : Equivalent (LTLFormula AP) := ⟨fun ϕ ψ => Worlds ϕ = Worlds ψ⟩

/--
Equivalence is reflexive.
-/
theorem equivalent_ltl_refl {AP: Type} (ϕ : LTLFormula AP) : ϕ ≡ ϕ := by
  simp only [Equivalent.Equiv]

/--
Equivalence is symmetric.
-/
theorem equivalent_ltl_symm {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ ≡ ψ) → (ψ ≡ ϕ) := by
  simp only [Equivalent.Equiv]
  intro h
  rw [h]

/--
Equivalence is transitive.
-/
theorem equivalent_ltl_trans {AP: Type} (ϕ ψ χ : LTLFormula AP) : (ϕ ≡ ψ) → (ψ ≡ χ) → (ϕ ≡ χ) := by
  simp only [Equivalent.Equiv]
  intro h₁ h₂
  rw [h₁]
  exact h₂

/-!
## Lemmas for Equivalence of LTL Forumulae

This includes preservation, duality, idependence, expansion, absorption, distribution, and other properties of equivalence.
-/
/--
Equivalence is preserved by negation.
-/
theorem equivalent_ltl_preserves_negation {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ ≡ ψ) ↔ ((¬ ϕ) ≡ (¬ ψ)) := by
  simp only [Equivalent.Equiv]
  constructor
  · intro h
    funext σ
    have h₁ : Worlds ϕ σ = Worlds ψ σ := by rw [h]
    simp only [Worlds, eq_iff_iff] at h₁
    simp only [Worlds, eq_iff_iff]
    rw [world_satisfies_not, world_satisfies_not]
    simp only [Not.not]
    rw [not_iff_not]
    exact h₁
  · intro h
    funext σ
    have h₁ : Worlds (¬ ϕ) σ = Worlds (¬ ψ) σ := by
      rw [funext_iff] at h
      exact h σ
    simp only [Worlds, eq_iff_iff] at h₁
    simp only [Worlds, eq_iff_iff]
    rw [world_satisfies_not, world_satisfies_not] at h₁
    simp only [Not.not] at h₁
    rw [not_iff_not] at h₁
    exact h₁

/--
Equivalence is preserved by always.
-/
theorem equivalent_ltl_preserves_always {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ ≡ ψ) → ((□ ϕ) ≡ (□ ψ)) := by
  simp only [Equivalent.Equiv]
  intro h
  funext σ
  unfold Worlds
  rw [world_satisfies_always, world_satisfies_always]
  simp only [eq_iff_iff]
  constructor
  · intro h'
    intro i
    specialize h' i
    have h₁ : Worlds ϕ (σ[i…]) = Worlds ψ (σ[i…]) := by rw [h]
    unfold Worlds at h₁
    rw [← h₁]
    assumption
  · intro h'
    intro i
    specialize h' i
    have h₁ : Worlds ϕ (σ[i…]) = Worlds ψ (σ[i…]) := by rw [h]
    unfold Worlds at h₁
    rw [h₁]
    assumption

/--
Double negation: `(¬ (¬ ϕ)) ≡ ϕ`.
-/
theorem ltl_double_negation {AP: Type} (ϕ : LTLFormula AP) : (¬ (¬ ϕ)) ≡ ϕ := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds, eq_iff_iff]
  rw [world_satisfies_not, world_satisfies_not]
  simp only [Not.not]
  rw [not_not]

/--
Duality for next: `(¬ (◯ ϕ)) ≡ (◯ (¬ ϕ))`.
-/
theorem ltl_duality_next {AP: Type} (ϕ : LTLFormula AP) : ((¬ (◯ ϕ)) ≡ (◯ (¬ ϕ))) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds, eq_iff_iff]
  rw [world_satisfies_not, world_satisfies_next, world_satisfies_next, world_satisfies_not]

/--
Duality for eventually: `(¬ (♢ ϕ)) ≡ (□ (¬ ϕ))`.
-/
theorem ltl_duality_eventually {AP: Type} (ϕ : LTLFormula AP) : ((¬ (♢ ϕ)) ≡ (□ (¬ ϕ))) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds, eq_iff_iff]
  rw [always_def]
  repeat rw [world_satisfies_not, world_satisfies_eventually]
  simp only [Not.not]
  rw [not_iff_not]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h
    use i
    simp only [Satisfaction.Satisfies]
    simp only [Satisfaction.Satisfies] at hi
    unfold world_satisfies_ltl world_satisfies_ltl
    simp only [Not.not]
    rw [not_not]
    exact hi
  · intro h
    obtain ⟨i, hi⟩ := h
    use i
    simp only [Satisfaction.Satisfies]
    simp only [Satisfaction.Satisfies] at hi
    unfold world_satisfies_ltl world_satisfies_ltl at hi
    simp only [Not.not] at hi
    rw [not_not] at hi
    exact hi

/--
Duality for always: `(¬ (□ ϕ)) ≡ (♢ (¬ ϕ))`.
-/
theorem ltl_duality_always {AP: Type} (ϕ : LTLFormula AP) : ((¬ (□ ϕ)) ≡ (♢ (¬ ϕ))) := by
  have h₀ : (¬ (♢ (¬ ϕ))) ≡ (□ (¬ (¬ ϕ))) := ltl_duality_eventually (¬ ϕ)
  have h₁ : (¬ (¬ ϕ)) ≡ ϕ := ltl_double_negation ϕ
  have h₂ : (□ (¬ (¬ ϕ))) ≡ (□ ϕ) := equivalent_ltl_preserves_always _ _ h₁
  have h₃ : (¬ ♢ (¬ ϕ)) ≡ (□ ϕ) := equivalent_ltl_trans _ _ _ h₀ h₂
  have h₄ : (¬ (¬ ♢ (¬ ϕ))) ≡ (¬ (□ ϕ)) := by
    rw [← equivalent_ltl_preserves_negation]
    assumption
  have h₅ : (¬ (¬ ♢ (¬ ϕ))) ≡ (♢ (¬ ϕ)) := ltl_double_negation _
  have h₆ : (¬ (□ ϕ)) ≡ (♢ (¬ ϕ)) := equivalent_ltl_trans _ _ _ h₄ h₅
  assumption

/--
Duality for until: `(¬ (ϕ 𝓤 ψ)) ≡ ((ϕ ∧ (¬ ψ)) 𝓦 ((¬ ϕ) ∧ (¬ ψ)))`.
-/
theorem ltl_duality_until {AP: Type} (ϕ ψ : LTLFormula AP) : (¬ (ϕ 𝓤 ψ)) ≡ ((ϕ ∧ (¬ ψ)) 𝓦 ((¬ ϕ) ∧ (¬ ψ))) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [propext_iff, world_satisfies_weakuntil]
  constructor
  · intro h
    rw [world_satisfies_not, world_satisfies_until] at h
    simp only [Not.not, not_exists] at h

    if h₁ : ∀ x, ¬ (Suffix σ x ⊨ ψ) then
      if h₂ : ∀ x, Suffix σ x ⊨ ϕ then
        right
        rw [world_satisfies_always]
        intro i
        specialize h₁ i
        specialize h₂ i
        rw [world_satisfies_and, world_satisfies_not]
        constructor <;> assumption
      else
        left
        have h' := satisfies_for_first_time_iff_satisfies (¬ ϕ) σ (by
          simp only [not_forall] at h₂
          obtain ⟨i, hi⟩ := h₂
          use i
          rw [world_satisfies_not]
          simp only [Not.not]
          assumption)
        obtain ⟨i, hi⟩ := h'
        obtain ⟨hl, hr⟩ := hi
        rw [world_satisfies_not] at hl
        simp only [Not.not] at hl
        rw [world_satisfies_until]
        use i
        rw [world_satisfies_and, world_satisfies_not]
        constructor
        · constructor
          · simp only [Not.not]
            assumption
          · rw [world_satisfies_not]
            specialize h₁ i
            assumption
        · intro k hk
          specialize hr k hk
          specialize h₁ k
          rw [world_satisfies_not] at hr
          simp only [Not.not, not_not] at hr
          rw [world_satisfies_and, world_satisfies_not]
          constructor <;> assumption
    else
      left
      have h₁' : ¬∀ (x : ℕ), Suffix σ x ⊨ (¬ ψ) := by
        simp only [Not.not, not_forall, not_not] at h₁
        obtain ⟨i, hi⟩ := h₁
        simp only [Not.not, not_forall]
        use i
        simp only [Satisfaction.Satisfies]
        unfold world_satisfies_ltl
        simp only [Not.not, not_not]
        simp only [Satisfaction.Satisfies] at hi
        assumption
      have h' := satisfies_for_first_time_iff_satisfies ψ σ (by
        simp only [Not.not, Satisfaction.Satisfies, not_forall] at h₁'
        obtain ⟨i, hi⟩ := h₁'
        use i
        simp only [Satisfaction.Satisfies]
        rw [world_satisfies_ltl] at hi
        simp only [Not.not, not_not] at hi
        assumption)
      obtain ⟨i, hi⟩ := h'
      obtain ⟨hl, hr⟩ := hi
      specialize h i
      simp only [And.and, not_and, not_forall, Classical.not_imp] at h
      apply h at hl
      obtain ⟨j, hj, hl⟩ := hl
      have hl' : ¬∀ (k : ℕ), Suffix σ k ⊨ ϕ := by
        by_contra hc
        simp only [Not.not, not_forall, not_exists, not_not] at hc
        specialize hc j
        contradiction
      have h'' := satisfies_for_first_time_iff_satisfies (¬ ϕ) σ (by
        simp only [Not.not, not_forall] at hl'
        obtain ⟨i, hi⟩ := hl'
        use i
        rw [world_satisfies_not]
        simp only [Not.not]
        assumption)
      obtain ⟨k, hk⟩ := h''
      rw [world_satisfies_until]
      use k
      have hk' : k < i := by
        have hkh : k ≤ j := by
          by_contra hc
          simp only [not_le] at hc
          obtain ⟨_, hk⟩ := hk
          specialize hk j hc
          contradiction
        apply Nat.lt_of_le_of_lt hkh hj
      let hr' := hr
      specialize hr k hk'
      obtain ⟨hkl, hkr⟩ := hk
      rw [world_satisfies_not] at hkl
      simp only [Not.not] at hr hkl hkl
      constructor
      · rw [world_satisfies_and, world_satisfies_not, world_satisfies_not]
        simp only [Not.not]
        constructor <;> assumption
      · intro m hm
        specialize hkr m hm
        rw [world_satisfies_and]
        have hmi : m < i := Nat.lt_trans hm hk'
        specialize hr' m hmi
        rw [world_satisfies_not]
        rw [world_satisfies_not] at hkr
        simp only [Not.not, not_not] at hkr
        constructor <;> assumption
  · intro h
    rw [world_satisfies_not, world_satisfies_until]
    simp only [Not.not, And.and, not_exists, not_and, not_forall, Classical.not_imp]
    cases h with
    | inl hl =>
      intro i hi
      rw [world_satisfies_until] at hl
      obtain ⟨j, hj, hl⟩ := hl
      if h' : j < i then
        use j, h'
        rw [world_satisfies_and, world_satisfies_not] at hj
        obtain ⟨hjl, hjr⟩ := hj
        simp only [Not.not] at hjl
        assumption
      else
        simp only [not_lt] at h'
        rw [Nat.le_iff_lt_or_eq] at h'
        cases h' with
        | inl hl' =>
          specialize hl i hl'
          rw [world_satisfies_and, world_satisfies_not] at hl
          obtain ⟨hll, hlr⟩ := hl
          simp only [Not.not] at hlr
          contradiction
        | inr hr' =>
          rw [hr'] at hi
          rw [world_satisfies_and, world_satisfies_not, world_satisfies_not] at hj
          obtain ⟨hjl, hjr⟩ := hj
          simp only [Not.not] at hjr
          contradiction
    | inr hr =>
      intro i hi
      rw [world_satisfies_always] at hr
      specialize hr i
      rw [world_satisfies_and] at hr
      simp only [And.and] at hr
      obtain ⟨hrl, hrr⟩ := hr
      rw [world_satisfies_not] at hrr
      simp only [Not.not] at hrr
      contradiction

/--
Duality for weak until: `(¬ (ϕ 𝓦 ψ)) ≡ ((ϕ ∧ (¬ ψ)) 𝓤 ((¬ ϕ) ∧ (¬ ψ)))`.
-/
theorem ltl_duality_weakuntil {AP: Type} (ϕ ψ : LTLFormula AP) : (¬ (ϕ 𝓦 ψ)) ≡ ((ϕ ∧ (¬ ψ)) 𝓤 ((¬ ϕ) ∧ (¬ ψ))) := by
  rw [equivalent_ltl_preserves_negation]
  have h₁ : (¬ (¬ (ϕ 𝓦 ψ))) ≡ (ϕ 𝓦 ψ) := ltl_double_negation (ϕ 𝓦 ψ)
  have h₂ : (ϕ 𝓦 ψ) ≡ (¬ ((ϕ ∧ (¬ ψ)) 𝓤 ((¬ ϕ) ∧ (¬ ψ)))) := by
    have h₃ := equivalent_ltl_symm _ _ (ltl_duality_until (ϕ ∧ (¬ ψ)) ((¬ ϕ) ∧ (¬ ψ)))
    have h₄ : (ϕ 𝓦 ψ) ≡ (((ϕ ∧ (¬ ψ)) ∧ (¬ (¬ ϕ) ∧ (¬ ψ))) 𝓦 (¬ ϕ ∧ (¬ ψ)) ∧ (¬ (¬ ϕ) ∧ (¬ ψ))) := by
      simp only [Equivalent.Equiv]
      funext σ
      simp only [Worlds]
      rw [propext_iff]
      repeat rw [world_satisfies_weakuntil]
      rw [world_satisfies_until]
      constructor
      · intro h
        simp only [Or.or] at h
        cases h with
        | inl hl =>
          left
          obtain ⟨j, hj, hl⟩ := hl
          have h' := satisfies_for_first_time_iff_satisfies ψ σ (by use j)
          obtain ⟨i, hi⟩ := h'
          obtain ⟨hil, hir⟩ := hi
          rw [world_satisfies_until]
          use i
          constructor
          · rw [world_satisfies_and, world_satisfies_not, world_satisfies_not, world_satisfies_and, world_satisfies_and, world_satisfies_not, world_satisfies_not]
            simp only [And.and, Not.not, not_and, not_not, Classical.imp_and_neg_imp_iff]
            assumption
          · intro k hk
            specialize hl k (by
              by_contra hc
              simp only [not_lt] at hc
              have hjj : j < i := Nat.lt_of_le_of_lt hc hk
              specialize hir j hjj
              simp only [Not.not] at hir
              contradiction)
            specialize hir k hk
            simp only [Not.not] at hir
            rw [world_satisfies_and, world_satisfies_not, world_satisfies_and, world_satisfies_and, world_satisfies_not, world_satisfies_not]
            simp only [And.and, Not.not, not_and, not_not]
            constructor
            · constructor <;> assumption
            · simp only [hl, not_true_eq_false, IsEmpty.forall_iff]
        | inr hr =>
          if h' : ∀ x, ¬ (Suffix σ x ⊨ ψ) then
            right
            rw [world_satisfies_always]
            intro i
            rw [world_satisfies_and, world_satisfies_not, world_satisfies_and, world_satisfies_and, world_satisfies_not, world_satisfies_not]
            simp only [And.and, Not.not, not_and, not_not]
            specialize h' i
            simp only [Not.not] at h'
            rw [world_satisfies_always] at hr
            specialize hr i
            constructor
            · constructor <;> assumption
            · simp only [hr, not_true_eq_false, IsEmpty.forall_iff]
          else
            left
            simp only [Not.not, not_forall, not_not] at h'
            have h'' := satisfies_for_first_time_iff_satisfies ψ σ h'
            rw [world_satisfies_until]
            obtain ⟨i, hi⟩ := h''
            obtain ⟨hil, hir⟩ := hi
            use i
            constructor
            · rw [world_satisfies_and, world_satisfies_not, world_satisfies_and, world_satisfies_not, world_satisfies_not, world_satisfies_and, world_satisfies_not, world_satisfies_not]
              simp only [And.and, Not.not, not_and, not_not, Classical.imp_and_neg_imp_iff]
              assumption
            · intro k hk
              rw [world_satisfies_and, world_satisfies_not, world_satisfies_and, world_satisfies_and, world_satisfies_not, world_satisfies_not]
              simp only [And.and, Not.not, not_and, not_not]
              specialize hir k hk
              simp only [Not.not] at hir
              rw [world_satisfies_always] at hr
              specialize hr k
              constructor
              · constructor <;> assumption
              · simp only [hr, not_true_eq_false, IsEmpty.forall_iff]
      · intro h
        simp only [Or.or] at h
        cases h with
        | inl hl =>
          left
          rw [world_satisfies_until] at hl
          obtain ⟨j, hj, hl⟩ := hl
          use j
          constructor
          · rw [world_satisfies_and, world_satisfies_not, world_satisfies_and, world_satisfies_not, world_satisfies_not, world_satisfies_and, world_satisfies_not, world_satisfies_not] at hj
            simp only [And.and, Not.not, not_and, not_not, Classical.imp_and_neg_imp_iff] at hj
            assumption
          · intro k hk
            specialize hl k hk
            rw [world_satisfies_and, world_satisfies_not, world_satisfies_and, world_satisfies_and, world_satisfies_not, world_satisfies_not] at hl
            simp only [And.and, Not.not, not_and, not_not] at hl
            obtain ⟨hl₁, hl₂⟩ := hl
            obtain ⟨hl₁l, hl₁r⟩ := hl₁
            assumption
        | inr hr =>
          right
          rw [world_satisfies_always]
          intro i
          rw [world_satisfies_always] at hr
          specialize hr i
          rw [world_satisfies_and, world_satisfies_not, world_satisfies_and, world_satisfies_and, world_satisfies_not, world_satisfies_not] at hr
          simp only [And.and, Not.not, not_and, not_not] at hr
          obtain ⟨hrl, hrr⟩ := hr
          obtain ⟨hrll, hrlr⟩ := hrl
          assumption
    apply equivalent_ltl_trans _ _ _ h₄ h₃
  apply equivalent_ltl_trans _ _ _ h₁ h₂

/--
Idempotence of eventually: `(♢ (♢ ϕ)) ≡ (♢ ϕ)`.
-/
theorem ltl_idempotence_eventually {AP: Type} (ϕ : LTLFormula AP) : (♢ (♢ ϕ)) ≡ (♢ ϕ) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds, eq_iff_iff]
  rw [world_satisfies_eventually, world_satisfies_eventually]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h
    rw [world_satisfies_eventually] at hi
    obtain ⟨j, hj⟩ := hi
    use i + j
    rw [Suffix.composition] at hj
    assumption
  · intro h
    obtain ⟨i, hi⟩ := h
    use 0
    rw [world_satisfies_eventually]
    use i
    rw [Suffix.composition]
    ring_nf
    assumption

/--
Idempotence of always: `(□ (□ ϕ)) ≡ (□ ϕ)`.
-/
theorem ltl_idempotence_always {AP: Type} (ϕ : LTLFormula AP) : (□ (□ ϕ)) ≡ (□ ϕ) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds, eq_iff_iff]
  rw [world_satisfies_always, world_satisfies_always]
  constructor
  · intro h
    intro i
    specialize h i
    rw [world_satisfies_always] at h
    specialize h 0
    rw [Suffix.composition] at h
    assumption
  · intro h
    intro i
    rw [world_satisfies_always]
    intro j
    rw [Suffix.composition]
    specialize h (i + j)
    assumption

/--
Idempotence of until from the left: `((ϕ 𝓤 ϕ) 𝓤 ψ) ≡ (ϕ 𝓤 ψ)`.
-/
theorem ltl_idempotence_until_left {AP: Type} (ϕ ψ : LTLFormula AP) : ((ϕ 𝓤 ϕ) 𝓤 ψ) ≡ (ϕ 𝓤 ψ) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds, eq_iff_iff]
  simp only [Satisfaction.Satisfies]
  rw [world_satisfies_ltl, world_satisfies_ltl]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := h
    obtain ⟨hj', hj''⟩ := hj
    use j
    constructor
    · assumption
    · intro k
      intro hk
      have hk' := hj'' k hk
      rw [world_satisfies_ltl] at hk'
      obtain ⟨k', hk''⟩ := hk'
      obtain ⟨hkl, hkr⟩ := hk''
      rw [Suffix.composition] at hkl
      specialize hkr 0
      cases c: k' with
      | zero =>
        rw [c] at hkl
        rw [Nat.add_zero] at hkl
        assumption
      | succ n =>
        have p : 0 < k' := by
          rw [c]
          apply Nat.zero_lt_succ
        specialize hkr p
        rw [Suffix.composition] at hkr
        rw [Nat.add_zero] at hkr
        assumption
  · intro h
    obtain ⟨j, hj⟩ := h
    use j
    obtain ⟨hl, hr⟩ := hj
    constructor
    · assumption
    · intro k
      intro hk
      rw [world_satisfies_ltl]
      use 0
      rw [Suffix.composition, Nat.add_zero]
      specialize hr k hk
      constructor
      · assumption
      · intro k'
        intro hk'
        simp only [not_lt_zero'] at hk'

/--
Idempotence of until from the right: `(ϕ 𝓤 (ψ 𝓤 ψ)) ≡ (ϕ 𝓤 ψ)`.
-/
theorem ltl_idempotence_until_right {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ 𝓤 (ψ 𝓤 ψ)) ≡ (ϕ 𝓤 ψ) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds, eq_iff_iff]
  simp only [Satisfaction.Satisfies]
  rw [world_satisfies_ltl, world_satisfies_ltl]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := h
    use j
    obtain ⟨hl, hr⟩ := hj
    rw [world_satisfies_ltl] at hl
    obtain ⟨j', hj'⟩ := hl
    obtain ⟨hjl, hjr⟩ := hj'
    rw [Suffix.composition] at hjl
    specialize hjr 0
    cases c: j' with
    | zero =>
      rw [c] at hjl
      rw [Nat.add_zero] at hjl
      constructor
      · assumption
      · assumption
    | succ n =>
      have p : 0 < j' := by
        rw [c]
        apply Nat.zero_lt_succ
      specialize hjr p
      rw [Suffix.composition] at hjr
      rw [Nat.add_zero] at hjr
      constructor
      · assumption
      · assumption

  · intro h
    obtain ⟨j, hj⟩ := h
    use j
    obtain ⟨hl, hr⟩ := hj
    constructor
    · rw [world_satisfies_ltl]
      use 0
      rw [Suffix.composition, Nat.add_zero]
      constructor
      · assumption
      · intro k
        intro hk
        simp only [not_lt_zero'] at hk
    · assumption

/--
Absorption of eventually by always eventually: `(♢ □ ♢ ϕ) ≡ (□ ♢ ϕ)`.
-/
theorem ltl_absorption_always_eventually {AP: Type} (ϕ : LTLFormula AP) : (♢ □ ♢ ϕ) ≡ (□ ♢ ϕ) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds, eq_iff_iff]
  rw [world_satisfies_eventually]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h
    rw [world_satisfies_always_eventually] at hi
    rw [world_satisfies_always_eventually]
    intro i'
    specialize hi i'
    obtain ⟨j, hj⟩ := hi
    use i + j
    rw [Suffix.composition] at hj
    rw [← Nat.add_assoc, Nat.add_comm i' i]
    rw [← Nat.add_assoc] at hj
    assumption
  · intro h
    use 0
    rw [Suffix.zero_identity]
    assumption

/--
Absorption of always by eventually always: `(□ ♢ □ ϕ) ≡ (♢ □ ϕ)`.
-/
theorem ltl_absorption_eventually_always {AP: Type} (ϕ : LTLFormula AP) : (□ ♢ □ ϕ) ≡ (♢ □ ϕ) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds, eq_iff_iff]
  rw [world_satisfies_always]
  constructor
  · intro h
    specialize h 0
    rw [Suffix.zero_identity] at h
    assumption
  · intro h
    intro i
    rw [world_satisfies_eventually_always] at h
    obtain ⟨i', hi⟩ := h
    rw [world_satisfies_eventually_always]
    use i'
    intro j
    specialize hi (i + j)
    rw [Suffix.composition]
    rw [← Nat.add_assoc]
    rw [← Nat.add_assoc, Nat.add_comm i' i] at hi
    assumption

/--
Expansion for until: `(ϕ 𝓤 ψ) ≡ (ψ ∨ (ϕ ∧ (◯ (ϕ 𝓤 ψ))))`.
-/
theorem ltl_expansion_until {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ 𝓤 ψ) ≡ (ψ ∨ (ϕ ∧ (◯ (ϕ 𝓤 ψ)))) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [world_satisfies_or, world_satisfies_and]
  simp only [Satisfaction.Satisfies, eq_iff_iff]
  constructor
  · intro h
    rw [world_satisfies_ltl] at h
    obtain ⟨j, hj⟩ := h
    obtain ⟨hl, hr⟩ := hj
    rw [world_satisfies_ltl]
    cases c: j with
    | zero =>
      rw [c] at hl
      rw [Suffix.zero_identity] at hl
      left
      assumption
    | succ n =>
      right
      have p : 0 < j := by
        rw [c]
        apply Nat.zero_lt_succ
      have hr' := hr 0 p
      rw [Suffix.zero_identity] at hr'
      constructor
      · assumption
      · repeat rw [world_satisfies_ltl]
        use n
        rw [Suffix.composition]
        rw [c] at hl
        rw [Nat.add_comm]
        constructor
        · assumption
        · intro k
          intro hk
          rw [Suffix.composition]
          have p' : k + 1 < j := by
            rw [c]
            have p'' : k + 1 < n + 1 := by
              apply Nat.succ_lt_succ
              assumption
            assumption
          specialize hr (k + 1) p'
          rw [Nat.add_comm]
          assumption
  · intro h
    rw [world_satisfies_ltl]
    cases h with
    | inl hl =>
        use 0
        rw [Suffix.zero_identity]
        constructor
        · assumption
        · simp only [not_lt_zero', IsEmpty.forall_iff, implies_true]
    | inr hr =>
        rw [world_satisfies_ltl] at hr
        obtain ⟨hll, hrr⟩ := hr
        repeat rw [world_satisfies_ltl] at hrr
        obtain ⟨j, hj⟩ := hrr
        use j + 1
        rw [Suffix.composition, Nat.add_comm] at hj
        obtain ⟨hjl, hjr⟩ := hj
        constructor
        · assumption
        · intro k
          intro hk
          cases c: k with
          | zero =>
            rw [Suffix.zero_identity]
            assumption
          | succ n =>
            rw [c] at hk
            rw [Nat.succ_lt_succ_iff] at hk
            specialize hjr n hk
            rw [Suffix.composition] at hjr
            rw [Nat.add_comm]
            assumption

/--
Expansion for weak until: `(ϕ 𝓦 ψ) ≡ (ψ ∨ (ϕ ∧ (◯ (ϕ 𝓦 ψ))))`.
-/
theorem ltl_expansion_weakuntil {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ 𝓦 ψ) ≡ (ψ ∨ (ϕ ∧ (◯ (ϕ 𝓦 ψ)))) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [propext_iff]
  rw [world_satisfies_weakuntil, world_satisfies_or, world_satisfies_and, world_satisfies_next, world_satisfies_weakuntil]
  simp only [Or.or, And.and]

  have huntil := ltl_expansion_until ϕ ψ
  simp only [Equivalent.Equiv] at huntil
  rw [funext_iff] at huntil
  specialize huntil σ
  simp only [Worlds] at huntil

  constructor
  · intro h
    cases h with
    | inl h =>
      rw [huntil] at h
      rw [world_satisfies_or, world_satisfies_and, world_satisfies_next] at h
      simp only [Or.or, And.and] at h
      cases h with
      | inl h =>
        left
        assumption
      | inr h =>
        right
        obtain ⟨hl, hr⟩ := h
        constructor
        · assumption
        · left
          assumption
    | inr h =>
      right
      rw [world_satisfies_always] at h
      constructor
      . specialize h 0
        rw [Suffix.zero_identity] at h
        assumption
      . right
        rw [world_satisfies_always]
        intro i
        specialize h (i + 1)
        rw [Suffix.composition]
        rw [Nat.add_comm]
        assumption
  · intro h
    cases h with
    | inl h =>
      left
      rw [huntil]
      rw [world_satisfies_or, world_satisfies_and, world_satisfies_next]
      left
      assumption
    | inr h =>
      obtain ⟨hl, hr⟩ := h
      cases hr with
      | inl h =>
        left
        rw [huntil]
        rw [world_satisfies_or, world_satisfies_and, world_satisfies_next]
        simp only [Or.or, And.and]
        right
        constructor <;> assumption
      | inr h =>
        right
        rw [world_satisfies_always] at h
        rw [world_satisfies_always]
        intro i
        cases c: i with
        | zero =>
          rw [Suffix.zero_identity]
          assumption
        | succ n =>
          specialize h n
          rw [Suffix.composition] at h
          rw [Nat.add_comm] at h
          assumption

/--
Expansion for eventually: `(♢ ϕ) ≡ (ϕ ∨ (◯ (♢ ϕ)))`.
-/
theorem ltl_expansion_eventually {AP: Type} (ϕ : LTLFormula AP) : (♢ ϕ) ≡ (ϕ ∨ (◯ (♢ ϕ))) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [world_satisfies_or]
  simp only [eq_iff_iff]
  constructor
  · intro h
    rw [world_satisfies_eventually] at h
    obtain ⟨i, hi⟩ := h
    cases c: i with
    | zero =>
      rw [c] at hi
      rw [Suffix.zero_identity] at hi
      left
      assumption
    | succ n =>
      right
      rw [world_satisfies_next]
      rw [world_satisfies_eventually]
      use n
      rw [Suffix.composition]
      rw [c] at hi
      rw [Nat.add_comm]
      assumption
  · intro h
    rw [world_satisfies_eventually]
    cases h with
    | inl hl =>
      use 0
      rw [Suffix.zero_identity]
      assumption
    | inr hr =>
      rw [world_satisfies_next] at hr
      rw [world_satisfies_eventually] at hr
      obtain ⟨j, hj⟩ := hr
      use j + 1
      rw [Suffix.composition, Nat.add_comm] at hj
      assumption

/--
Expansion for always: `(□ ϕ) ≡ (ϕ ∧ (◯ (□ ϕ)))`.
-/
theorem ltl_expansion_always {AP: Type} (ϕ : LTLFormula AP) : (□ ϕ) ≡ (ϕ ∧ (◯ (□ ϕ))) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [world_satisfies_and]
  simp only [eq_iff_iff]
  rw [world_satisfies_next]
  repeat rw [world_satisfies_always]
  constructor
  · intro h
    constructor
    · specialize h 0
      rw [Suffix.zero_identity] at h
      assumption
    · intro i
      specialize h (i + 1)
      rw [Suffix.composition, Nat.add_comm]
      assumption
  · intro h
    intro i
    obtain ⟨hl, hr⟩ := h
    cases c: i with
    | zero =>
      rw [Suffix.zero_identity]
      assumption
    | succ n =>
      specialize hr n
      rw [Suffix.composition, Nat.add_comm] at hr
      assumption

/--
Distributivity of next over until: `(◯ (ϕ 𝓤 ψ)) ≡ ((◯ ϕ) 𝓤 (◯ ψ))`.
-/
theorem ltl_distributive_next_until {AP: Type} (ϕ ψ : LTLFormula AP) : (◯ (ϕ 𝓤 ψ)) ≡ ((◯ ϕ) 𝓤 (◯ ψ)) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [world_satisfies_next]
  repeat rw [world_satisfies_until]
  simp only [eq_iff_iff]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := h
    use j
    rw [Suffix.composition] at hj
    rw [world_satisfies_next]
    rw [Suffix.composition]
    rw [Nat.add_comm]
    obtain ⟨hl, hr⟩ := hj
    constructor
    · assumption
    · intro k
      intro hk
      specialize hr k hk
      rw [world_satisfies_next]
      rw [Suffix.composition]
      rw [Suffix.composition] at hr
      rw [Nat.add_comm]
      assumption
  · intro h
    obtain ⟨j, hj⟩ := h
    use j
    rw [world_satisfies_next] at hj
    rw [Suffix.composition] at hj
    rw [Suffix.composition]
    rw [Nat.add_comm]
    obtain ⟨hl, hr⟩ := hj
    constructor
    · assumption
    · intro k
      intro hk
      specialize hr k hk
      rw [world_satisfies_next] at hr
      rw [Suffix.composition]
      rw [Suffix.composition] at hr
      rw [Nat.add_comm]
      assumption

/--
Distributivity of or over eventually: `(♢ (ϕ ∨ ψ)) ≡ ((♢ ϕ) ∨ (♢ ψ))`.
-/
theorem ltl_distributive_eventually_or {AP: Type} (ϕ ψ : LTLFormula AP) : (♢ (ϕ ∨ ψ)) ≡ ((♢ ϕ) ∨ (♢ ψ)) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [world_satisfies_eventually]
  repeat rw [world_satisfies_or]
  simp only [eq_iff_iff]
  constructor
  · intro h
    repeat rw [world_satisfies_eventually]
    obtain ⟨i, hi⟩ := h
    rw [world_satisfies_or] at hi
    cases hi with
    | inl hl =>
      left
      use i
    | inr hr =>
      right
      use i
  · intro h
    cases h with
    | inl hl =>
      rw [world_satisfies_eventually] at hl
      obtain ⟨i, hi⟩ := hl
      use i
      rw [world_satisfies_or]
      left
      assumption
    | inr hr =>
      rw [world_satisfies_eventually] at hr
      obtain ⟨i, hi⟩ := hr
      use i
      rw [world_satisfies_or]
      right
      assumption

/--
Distributivity of and over always: `(□ (ϕ ∧ ψ)) ≡ ((□ ϕ) ∧ (□ ψ))`.
-/
theorem ltl_distributive_always_and {AP: Type} (ϕ ψ : LTLFormula AP) : (□ (ϕ ∧ ψ)) ≡ ((□ ϕ) ∧ (□ ψ)) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [world_satisfies_always]
  repeat rw [world_satisfies_and]
  simp only [eq_iff_iff]
  constructor
  · intro h
    repeat rw [world_satisfies_always]
    constructor
    · intro i
      specialize h i
      rw [world_satisfies_and] at h
      obtain ⟨hl, hr⟩ := h
      assumption
    · intro i
      specialize h i
      rw [world_satisfies_and] at h
      obtain ⟨hl, hr⟩ := h
      assumption
  · intro h
    repeat rw [world_satisfies_always] at h
    intro i
    obtain ⟨hl, hr⟩ := h
    specialize hl i
    specialize hr i
    rw [world_satisfies_and]
    constructor
    · assumption
    · assumption


/-!
## Expansion Law Solutions

Characterization of until and weak until as least and greatest solutions of the expansion law respectively.
-/
/--
A solution of the expansion law from below is one that contains all the worlds that it would contain  if it were to be the exact solution.
-/
def solution_of_expansion_law_lower {AP: Type} (ϕ ψ : LTLFormula AP) (P : Set (World AP)) : Prop := (Worlds ψ ∪ {σ ∈ Worlds ϕ | σ[1…] ∈ P}) ⊆ P

/--
A solution of the expansion law from above is one that contains only the worlds that it would contain if it were to be the exact solution.
-/
def solution_of_expansion_law_upper {AP: Type} (ϕ ψ : LTLFormula AP) (P : Set (World AP)) : Prop := P ⊆ (Worlds ψ ∪ {σ ∈ Worlds ϕ | σ[1…] ∈ P})

/--
Until is the least solution of the expansion law.
-/
theorem until_least_solution_of_expansion_law {AP: Type} (ϕ ψ : LTLFormula AP) : (solution_of_expansion_law_lower ϕ ψ (Worlds (ϕ 𝓤 ψ))) ∧ (∀ P, (solution_of_expansion_law_lower ϕ ψ P) → Worlds (ϕ 𝓤 ψ) ⊆ P) := by
  unfold solution_of_expansion_law_lower
  unfold Worlds
  simp only [Set.union_subset_iff, and_imp]
  constructor

  -- we first show that it is indeed a solution
  · constructor
    · intro σ
      intro h
      rw [Set.mem_def] at h
      rw [Set.mem_def]
      rw [world_satisfies_until]
      use 0
      rw [Suffix.zero_identity]
      constructor
      · assumption
      · intro k
        intro hk
        simp only [not_lt_zero'] at hk
    · intro σ
      intro h
      rw [Set.mem_sep_iff] at h
      rw [Set.mem_def] at h
      rw [Set.mem_def]
      obtain ⟨hl, hr⟩ := h
      rw [Set.mem_def] at hr
      rw [world_satisfies_until]
      rw [world_satisfies_until] at hr
      obtain ⟨j, hj⟩ := hr
      rw [Suffix.composition] at hj
      use (1 + j)
      obtain ⟨hjl, hjr⟩ := hj
      constructor
      · assumption
      · intro k
        intro hk
        cases c: k with
        | zero =>
          rw [Suffix.zero_identity]
          assumption
        | succ n =>
          rw [c] at hk
          rw [Nat.add_comm 1 j] at hk
          rw [Nat.succ_lt_succ_iff] at hk
          specialize hjr n hk
          rw [Suffix.composition] at hjr
          rw [Nat.add_comm]
          assumption

  -- now we show that it is the least solution
  · intro P
    intro h
    intro h₁
    rw [Set.subset_def]
    intro σ
    intro h'
    rw [Set.mem_def] at h'
    rw [world_satisfies_until] at h'
    obtain ⟨j, hj⟩ := h'
    obtain ⟨hjl, hjr⟩ := hj
    rw [Set.subset_def] at h
    specialize h (σ[j…])
    rw [Set.mem_def] at h
    apply h at hjl

    -- we perform backwards induction on j
    let b (k: ℕ) : ∀ (n: ℕ), (j = n + k) → (σ[n…]) ∈ P := by
      induction k with
      | zero =>
        intro n
        intro hn
        simp only [add_zero] at hn
        rw [← hn]
        assumption
      | succ m ih =>
        intro n
        intro hn
        rw [Nat.add_comm m 1] at hn
        rw [← Nat.add_assoc] at hn
        specialize ih (n + 1) hn
        have h₀ : 0 < (1 + m) := by
          apply Nat.zero_lt_of_ne_zero
          rw [Nat.add_comm]
          apply Nat.succ_ne_zero
        rw [← @Nat.add_lt_add_iff_left n, Nat.add_zero, ← Nat.add_assoc, ← hn] at h₀
        specialize hjr n h₀
        rw [Set.subset_def] at h₁
        specialize h₁ (σ[n…])
        apply h₁
        rw [Set.mem_sep_iff]
        rw [Set.mem_def]
        constructor
        · assumption
        · rw [Suffix.composition]
          assumption

    have h₀ : σ[0…] ∈ P := by
      apply b j 0
      simp only [zero_add]

    rw [Suffix.zero_identity] at h₀
    assumption

/--
Weak until is the greatest solution of the expansion law.
-/
theorem weakuntil_greatest_solution_of_expansion_law {AP: Type} (ϕ ψ : LTLFormula AP) : (solution_of_expansion_law_upper ϕ ψ (Worlds (ϕ 𝓦 ψ))) ∧ (∀ P, (solution_of_expansion_law_upper ϕ ψ P) → P ⊆ Worlds (ϕ 𝓦 ψ)) := by
  unfold solution_of_expansion_law_upper Worlds
  simp only [And.and]

  have hwu := ltl_expansion_weakuntil ϕ ψ
  simp only [Equivalent.Equiv] at hwu
  rw [funext_iff] at hwu

  constructor

  -- we first show that it is indeed a solution
  · rw [Set.subset_def]
    intro σ hσ
    rw [Set.mem_def] at hσ
    rw [Set.union_def, Set.mem_def, Set.setOf_app_iff, Set.mem_def, Set.mem_def, Set.setOf_app_iff, Set.mem_def, Set.mem_def]
    specialize hwu σ
    simp only [Worlds] at hwu
    rw [hwu] at hσ
    rw [world_satisfies_or, world_satisfies_and, world_satisfies_next] at hσ
    simp only [Or.or, And.and] at hσ
    assumption

  -- now we show that it is the greatest solution
  · intro P h
    rw [Set.subset_def, Set.union_def] at h
    rw [Set.subset_def]
    intro σ hσ
    rw [Set.mem_def]
    rw [world_satisfies_weakuntil, world_satisfies_until, world_satisfies_always]

    if hψ : ∀ i, ¬ (Suffix σ i ⊨ ψ) then
      let h' (i : ℕ) : (Suffix σ i ⊨ ϕ) ∧ (Suffix σ (i + 1) ∈ P) := by
        induction i with
        | zero =>
          specialize h σ hσ
          specialize hψ 0
          rw [Suffix.zero_identity] at hψ
          rw [Suffix.zero_identity]
          simp only [Not.not] at hψ
          rw [Set.mem_def, Set.setOf_app_iff, Set.mem_def, Set.mem_def] at h
          simp only [hψ, false_or] at h
          rw [Set.setOf_app_iff, Set.mem_def] at h
          obtain ⟨hl, hr⟩ := h
          ring_nf
          constructor <;> assumption
        | succ k ih =>
          obtain ⟨hl, hr⟩ := ih
          specialize hψ (k + 1)
          simp only [Not.not] at hψ
          specialize h (Suffix σ (k + 1)) hr
          rw [Set.mem_def, Set.setOf_app_iff, Set.mem_def, Set.mem_def] at h
          simp only [hψ, false_or] at h
          rw [Set.setOf_app_iff, Set.mem_def] at h
          rw [Suffix.composition] at h
          assumption

      right
      intro i
      specialize h' i
      obtain ⟨hl, hr⟩ := h'
      assumption
    else
      simp only [Not.not, not_forall, not_not] at hψ
      have hψ' := satisfies_for_first_time_iff_satisfies ψ σ hψ
      obtain ⟨i, hi⟩ := hψ'
      obtain ⟨hil, hir⟩ := hi
      left
      use i
      simp only [And.and, hil, true_and]

      let h' (k : ℕ) : k < i → ((Suffix σ k ⊨ ϕ) ∧ (Suffix σ (k + 1) ∈ P)) := by
        induction k with
        | zero =>
          if c : 0 < i then
            simp only [c, zero_add, forall_const]
            specialize hir 0 c
            simp only [Not.not] at hir
            specialize h σ hσ
            rw [Set.mem_def, Set.setOf_app_iff, Set.mem_def, Set.mem_def] at h
            rw [Suffix.zero_identity] at hir
            simp only [hir, false_or] at h
            rw [Set.setOf_app_iff, Set.mem_def] at h
            rw [Suffix.zero_identity]
            assumption
          else
            simp only [c, zero_add, IsEmpty.forall_iff]
        | succ n ih =>
          if c : n + 1 < i then
            simp only [c, forall_const]
            have hn : n < i := Nat.lt_trans (lt_add_one n) c
            specialize ih hn
            obtain ⟨hl, hr⟩ := ih
            specialize h (Suffix σ (n + 1)) hr
            rw [Set.mem_def, Set.setOf_app_iff, Set.mem_def, Set.mem_def] at h
            rw [Set.setOf_app_iff, Set.mem_def] at h
            specialize hir (n + 1) c
            simp only [Not.not] at hir
            simp only [hir, false_or] at h
            rw [Suffix.composition] at h
            assumption
          else
            simp only [c, IsEmpty.forall_iff]

      intro k hk
      specialize h' k hk
      obtain ⟨hl, hr⟩ := h'
      assumption

/-!
## Satisfaction of PL Formulae

Defines satisfaction of propositional logic formulae by sets of atomic propositions.
-/
instance {AP: Type} : Satisfaction (Set AP) (PLFormula AP) := ⟨fun A Φ ↦ A ⊨ Φ.toLTLFormula⟩

/--
Satisfaction of negation for PL formulae.
-/
def set_satisfies_not {AP: Type} (σ : Set AP) (ϕ : PLFormula AP) : (σ ⊨ (¬ ϕ)) ↔ (¬ (σ ⊨ ϕ)) := by
  simp only [Satisfaction.Satisfies]
  rfl

/--
Satisfaction of conjunctions for PL formulae.
-/
def set_satisfies_and {AP: Type} (σ : Set AP) (ϕ₁ ϕ₂ : PLFormula AP) : (σ ⊨ (ϕ₁ ∧ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∧ (σ ⊨ ϕ₂)) := by
  simp only [Satisfaction.Satisfies]
  rfl

/--
Satisfaction of disjunction for PL formulae.
-/
def set_satisfies_or {AP: Type} (σ : Set AP) (ϕ₁ ϕ₂ : PLFormula AP) : (σ ⊨ (ϕ₁ ∨ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∨ (σ ⊨ ϕ₂)) := by
  rw [PLFormula.or_def, set_satisfies_not, set_satisfies_and, set_satisfies_not, set_satisfies_not]
  simp only [Not.not, And.and]
  rw [not_and, not_not, ← or_iff_not_imp_left]
  rfl
