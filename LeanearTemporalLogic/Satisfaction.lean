/-
# Satisfaction in Linear Temporal Logic

This module provides the formalization of the satisfaction relation between different objects in the context of Linear Temporal Logic (LTL) and Linear Time Properties (LT properties). Satisfaction also forms the basis for the notion of equivalence.

This module provides several results related to satisfaction and equivalence of these objects, including using them as the basis for characterizing certain kinds of objects.
-/
import Mathlib
import LeanearTemporalLogic.AbstractWorlds
import LeanearTemporalLogic.LTL
import LeanearTemporalLogic.TransitionSystems
import LeanearTemporalLogic.LTProperty

set_option linter.flexible true

/-!
## Satisfaction and Equivalence Type Classes

These type classes provide a generic framework for defining satisfaction and equivalence relations for various models and formulae.
-/
/-- The `Satisfaction` type class defines a satisfaction relation between models and formulae. -/
class Satisfaction (α : Type u) (β : Type v) where
  Satisfies : α → β → Prop

infixl:70 (priority := high) " ⊨ " => Satisfaction.Satisfies

class Equivalent (α : Type) where
  Equiv : α → α → Prop

infixl:70 (priority := high) " ≡ " => Equivalent.Equiv

/-!
## Worlds and Traces

A world is an infinite sequence of states, each being a set of atomic propositions. Prefixes and suffixes of worlds are used to define temporal operators.
-/
/-- A `World` is an infinite sequence of sets of atomic propositions. -/
abbrev World := AbstractWorld
/-- A `FiniteWorld` is a finite sequence of sets of atomic propositions. -/
abbrev FiniteWorld := AbstractFiniteWorld

/--
A suffix of a world `w` starting at index `i` is a world `w'` such that `w'(j) = w(i+j)` for all `j`.
Denoted as `w[i…]`.
-/
def Suffix {AP: Type} (σ : World AP) (i : ℕ) : World AP := fun j => σ (i + j)

syntax:60 term "[" term "…]" : term
macro_rules
  | `($σ[$i…]) => `(Suffix $σ $i)

/--
Composition of suffixes: taking a suffix of a suffix is the same as taking a single suffix at the sum of the indices.
-/
theorem Suffix.composition {AP: Type} (σ : World AP) (i j : ℕ) : σ[i…][j…] = σ[i+j…] := by
  funext k
  unfold Suffix
  rw [Nat.add_assoc]

/--
The suffix at index 0 is the world itself.
-/
theorem Suffix.zero_identity {AP: Type} (σ : World AP) : σ[0…] = σ := by
  funext k
  unfold Suffix
  rw [Nat.zero_add]

/--
A prefix of a world is its initial segment of finite length `n`.
-/
def Prefix {AP: Type} (σ : World AP) (n: ℕ) : FiniteWorld AP := ⟨n, fun i => σ i⟩

/--
A prefix of a prefix, of length `m ≤ ω.n`.
-/
def PrefixOfPrefix {AP: Type} (ω : FiniteWorld AP) (m : ℕ) (h: m ≤ ω.n) : FiniteWorld AP := ⟨m, fun i => ω.f (Fin.castLE (by simp only [add_le_add_iff_right, h]) i)⟩

/--
The set of all prefixes of a world.
-/
def pref {AP: Type} (σ: World AP) : Set (FiniteWorld AP) := fun ω => ∃ (n: ℕ), ω = Prefix σ n

/-!
## Satisfaction of LTL Formulae

Defines the recursive satisfaction relation for LTL formulae by worlds, and provides instances for worlds and states.
-/
section
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

end section

section
open TransitionSystem

/-!
## Satisfaction of LT Properties by Transition Systems
-/
/--
Satisfaction of LT properties by transition systems without terminal states. For this, both the transition system and the property must be defined over the same set of atomic propositions.

The motivation for restricting to transition systems without terminal states is that this guarantees infinite traces that can act as worlds for the LT property. Infinite traces are easier to work with in many practical applications.
-/
instance {AP: Type} : Satisfaction (TransitionSystemWTS AP) (LTProperty AP) := ⟨fun TSwts P ↦ TracesWTS TSwts ⊆ P⟩

/--
Satisfaction of LT properties by states of transition systems without terminal states.
-/
instance {AP: Type} {TSwts: TransitionSystemWTS AP} : Satisfaction (TSwts.S) (LTProperty AP) := ⟨fun s P ↦ TracesFromStateWTS s ⊆ P⟩

/--
Membership of an infinite trace in an LT property.
-/
instance {AP: Type} : Membership (InfiniteTrace AP) (LTProperty AP) := ⟨fun P π ↦ by
  rw [LTProperty] at P
  exact π ∈ P⟩

/--
Satisfaction of a set of worlds by a transition system without terminal states.
-/
instance {AP: Type} : Satisfaction (TransitionSystemWTS AP) (Set (World AP)) := ⟨fun TSwts P ↦ TracesWTS TSwts ⊆ P⟩

/--
A transition system satisfies an LT property iff the traces of all its paths are in the property.
-/
theorem ltproperty_satisfaction_allPaths {AP: Type} (TSwts: TransitionSystemWTS AP) (P: LTProperty AP) : TSwts ⊨ P ↔ ∀ π, (h: π ∈ Paths TSwts.TS) → TraceFromPathWTS π h ∈ P := by
  simp only [Satisfaction.Satisfies]
  rw [TracesWTS]
  simp only [Set.mem_setOf_eq, Set.iUnion_subset_iff]
  constructor
  · intro h
    intro π
    intro h'
    rw [Paths] at h'
    simp only [Set.mem_setOf_eq] at h'
    rw [isPath] at h'
    obtain ⟨hinit, hmax⟩ := h'
    rw [isInitialPathFragment] at hinit
    specialize h (startStatePathFragment π)
    apply h at hinit
    rw [TracesFromInitialStateWTS] at hinit
    rw [Set.setOf_subset] at hinit
    specialize hinit (TraceFromPathWTS π h')
    apply hinit
    use π
    use path_starts_from_startState π h'
    unfold TraceFromPathFromInitialStateWTS
    simp only
  · intro h
    intro s
    intro h'
    unfold TracesFromInitialStateWTS
    rw [Set.setOf_subset]
    intro trace
    intro h''
    obtain ⟨π, hπ⟩ := h''
    obtain ⟨hπ', hπ''⟩ := hπ
    specialize h π
    have h₀: π ∈ Paths TSwts.TS := by
      rw [Paths]
      rw [PathsFromState] at hπ'
      simp only [Set.mem_setOf_eq] at hπ'
      simp only [Set.mem_setOf_eq]
      unfold isPath
      obtain ⟨hl, hr⟩ := hπ'
      constructor
      · unfold isInitialPathFragment
        rw [hr]
        assumption
      · assumption
    apply h at h₀
    rw [TraceFromPathFromInitialStateWTS] at hπ''
    rw [← hπ''] at h₀
    assumption

/-!
## Trace Inclusion and LT Properties

Relates trace inclusion between systems to satisfaction of LT properties.
-/
/--
Trace inclusion between systems is equivalent to preservation of satisfaction for all LT properties.
-/
theorem trace_inclusion_and_LTProperties {AP: Type} (TSwts₁ TSwts₂: TransitionSystemWTS AP) : (TracesWTS TSwts₁ ⊆ TracesWTS TSwts₂) ↔ ∀ (P: LTProperty AP), TSwts₂ ⊨ P → TSwts₁ ⊨ P := by
  simp only [Satisfaction.Satisfies]
  constructor
  · intro h
    intro P
    intro h'
    rw [Set.subset_def]
    rw [Set.subset_def] at h
    rw [Set.subset_def] at h'
    intro σ
    intro h''
    specialize h σ
    apply h at h''
    specialize h' σ h''
    assumption
  · intro h
    specialize h (TracesWTS TSwts₂)
    simp only [subset_refl, forall_const] at h
    assumption

/--
Trace equivalence between systems is the equivalence of the sets of their traces.
-/
def trace_equivalence {AP: Type} (TS₁ TS₂: TransitionSystem AP) : Prop := Traces TS₁ = Traces TS₂

/--
Trace equivalence for transition systems without terminal states.
-/
def trace_equivalence_wts {AP: Type} (TSwts₁ TSwts₂: TransitionSystemWTS AP) : Prop := TracesWTS TSwts₁ = TracesWTS TSwts₂

/--
Two systems are trace equivalent iff they satisfy the same LT properties.
-/
theorem trace_equivalence_and_LTProperties {AP: Type} (TSwts₁ TSwts₂: TransitionSystemWTS AP) : (trace_equivalence_wts TSwts₁ TSwts₂) ↔ ∀ (P: LTProperty AP), TSwts₁ ⊨ P ↔ TSwts₂ ⊨ P := by
  rw [trace_equivalence_wts]
  constructor
  · intro h
    have h₀ : TracesWTS TSwts₁ ⊆ TracesWTS TSwts₂ := by rw [h]
    rw [trace_inclusion_and_LTProperties] at h₀
    have h₁ : TracesWTS TSwts₂ ⊆ TracesWTS TSwts₁ := by rw [h]
    rw [trace_inclusion_and_LTProperties] at h₁
    intro P
    constructor
    · apply h₁
    · apply h₀
  · intro h
    rw [Set.Subset.antisymm_iff]
    rw [trace_inclusion_and_LTProperties, trace_inclusion_and_LTProperties]
    constructor
    · intro P
      specialize h P
      rw [iff_def'] at h
      obtain ⟨h₁, h₂⟩ := h
      apply h₁
    · intro P
      specialize h P
      rw [iff_def'] at h
      obtain ⟨h₁, h₂⟩ := h
      apply h₂

/-!
## Invariants

An LT property is an invariant with condition `ϕ` if it is the set of worlds where every state satisfies `ϕ`.
-/
def isInvariantWithCondition {AP: Type} (P: LTProperty AP) (ϕ: PLFormula AP) : Prop := P = {σ | ∀ (n: ℕ), σ n ⊨ ϕ}
/--
An LT property is an invariant if it is an invariant with some condition.
-/
def isInvariant {AP: Type} (P: LTProperty AP) : Prop := ∃ (ϕ : PLFormula AP), isInvariantWithCondition P ϕ

/--
A system satisfies an invariant property iff all reachable states satisfy the invariant condition.
-/
theorem invariant_satisfaction_reachability {AP: Type} (TSwts: TransitionSystemWTS AP) (P: LTProperty AP) (h: isInvariant P) : TSwts ⊨ P ↔ (∃ (ϕ : PLFormula AP), (isInvariantWithCondition P ϕ) ∧ (∀ s ∈ Reach TSwts.TS, TSwts.L s ⊨ ϕ)) := by
  rw [ltproperty_satisfaction_allPaths]
  rw [isInvariant] at h
  obtain ⟨ϕ, hϕ⟩ := h
  unfold isInvariantWithCondition at hϕ
  obtain ⟨TS, hTS⟩ := TSwts
  let hTS' := hTS
  rw [hasNoTerminalStates] at hTS
  constructor
  · intro h'
    use ϕ
    constructor
    · assumption
    · intro s
      intro hs
      rw [Reach] at hs
      simp only [Set.mem_setOf_eq] at hs
      unfold isReachableState at hs
      obtain ⟨e, he⟩ := hs
      obtain ⟨hel, her⟩ := he
      let πtail : FinitePathFragment TS := finiteExecutionFragmentToFinitePathFragment e
      have htail : πtail.states = e.states := by
        unfold πtail finiteExecutionFragmentToFinitePathFragment
        simp only
      have en : e.n = πtail.n := by
        unfold πtail finiteExecutionFragmentToFinitePathFragment
        simp only
      simp only at en
      simp only at htail
      have hhead : ∃ π', π' ∈ PathsFromState s := path_originates_from_state_if_noTerminalState hTS s
      obtain ⟨πhead, hπhead⟩ := hhead
      simp only at πhead
      simp only at h'
      simp only at s
      cases c: πhead with
      | finite p =>
        rw [c] at hπhead
        unfold PathsFromState at hπhead
        simp only [Set.mem_setOf_eq] at hπhead
        obtain ⟨hπheadmax, _⟩ := hπhead
        unfold isMaximalPathFragment endStatePathFragment at hπheadmax
        simp only at hπheadmax
        specialize hTS (p.states (Fin.last p.n))
        contradiction
      | infinite p =>
        rw [c] at hπhead
        obtain ⟨headStates, headValid⟩ := p

        unfold PathsFromState startStatePathFragment at hπhead
        simp only [Set.mem_setOf_eq] at hπhead
        obtain ⟨_, headState0⟩ := hπhead

        -- combine πtail and πhead to form a path
        let π := PathFragment.infinite (PathFragment.concatenate_finite_and_infinite πtail ⟨headStates, headValid⟩ (by
          rw [htail]
          unfold endStateExecutionFragment at her
          simp only
          rw [headState0]
          have heq : Fin.last e.n = Fin.last πtail.n := by
            rw [← Fin.natCast_eq_last]
            rw [← Fin.natCast_eq_last]
            simp only [en, Fin.natCast_eq_last]
          rw [← heq]
          assumption
          ))

        have hπ : π ∈ Paths TS := by
          unfold Paths isPath isInitialPathFragment isMaximalPathFragment endStatePathFragment
          simp only [Set.mem_setOf_eq]
          constructor
          · unfold startStatePathFragment π
            simp only
            unfold isInitialExecutionFragment startStateExecutionFragment at hel
            simp only at hel
            unfold PathFragment.concatenate_finite_and_infinite
            simp only [Nat.cast_zero, zero_le, Nat.sub_eq_zero_of_le]
            cases cc: e.n with
            | zero =>
              rw [headState0]
              simp only [← en, cc, lt_self_iff_false, ↓reduceIte]
              unfold endStateExecutionFragment at her
              rw [← Fin.natCast_eq_last] at her
              simp only [cc, Nat.cast_zero] at her
              rw [← her]
              simp only [hel]
            | succ m =>
              rw [htail]
              simp only [← en, cc, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true, ↓reduceIte]
              apply hel
          · unfold π
            simp only

        specialize h' π hπ
        rw [hϕ] at h'
        rw [Set.mem_def] at h'
        rw [Set.setOf_app_iff] at h'
        specialize h' e.n

        have hs : (@TraceFromPathWTS AP ⟨TS, hTS⟩ π hπ) e.n = TS.L s := by
          unfold TraceFromPathWTS InfiniteTraceFromInfinitePathFragment
          unfold Paths isPath at hπ
          simp only [Set.mem_setOf_eq] at hπ
          obtain ⟨hπl, hπr⟩ := hπ
          rw [maximalIffInfinitePathFragment hTS'] at hπr
          simp only
          match c: π with
          | PathFragment.finite p =>
            simp only
            contradiction
          | PathFragment.infinite p =>
            simp only
            unfold endStateExecutionFragment at her
            unfold π at c
            simp only [PathFragment.infinite.injEq] at c
            rw [← c]
            unfold PathFragment.concatenate_finite_and_infinite
            simp only [en, lt_self_iff_false, ↓reduceIte, tsub_self]
            rw [headState0]

        rw [hs] at h'
        assumption
  · intro h'
    intro π
    intro hπ
    simp only at π
    simp only at hπ
    obtain ⟨Φ, hΦ⟩ := h'
    obtain ⟨hΦl, hΦr⟩ := hΦ
    unfold isInvariantWithCondition at hΦl
    simp only at hΦr
    rw [hΦl, Set.mem_def, Set.setOf_app_iff]
    intro n
    unfold TraceFromPathWTS InfiniteTraceFromInfinitePathFragment
    cases π with
    | finite _ =>
      unfold Paths isPath at hπ
      simp only [Set.mem_setOf_eq] at hπ
      obtain ⟨hπl, hπr⟩ := hπ
      simp only
      contradiction
    | infinite p =>
      simp only
      have hreach : p.states n ∈ Reach TS := by
        unfold Reach isReachableState
        simp only [Set.mem_setOf_eq]
        let eInf := infinitePathFragmentToInfiniteExecutionFragment p
        let e : FiniteExecutionFragment TS := ⟨n, fun i => eInf.states i, fun i => eInf.actions i, by
          intro i
          simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.coeSucc_eq_succ, Fin.val_succ]
          exact eInf.valid i⟩
        use e
        constructor
        · unfold isInitialExecutionFragment startStateExecutionFragment
          simp only
          unfold Paths isPath at hπ
          simp only [Set.mem_setOf_eq] at hπ
          obtain ⟨hπl, hπr⟩ := hπ
          unfold isInitialPathFragment startStatePathFragment at hπl
          simp only at hπl
          unfold e eInf infinitePathFragmentToInfiniteExecutionFragment
          simp only [Fin.val_zero]
          assumption
        · unfold endStateExecutionFragment e eInf infinitePathFragmentToInfiniteExecutionFragment
          simp only [Fin.val_natCast, Fin.coe_castSucc, Fin.val_succ, id_eq, eq_mpr_eq_cast, Fin.val_last]
      exact hΦr (p.states n) hreach

/-!
## Safety Properties

A property is a safety property if every violation can be detected by a finite prefix.
-/
def isSafetyProperty {AP: Type} (P: LTProperty AP) : Prop := ∀ (σ: World AP), σ ∉ P → ∃ n, ∀ σ', (Prefix σ' n = Prefix σ n) → σ' ∉ P

/--
A finite world is a bad prefix for a safety property if all its extensions violate the property.
-/
def isBadPrefix {AP: Type} (P: LTProperty AP) (ω: FiniteWorld AP) : Prop := isSafetyProperty P ∧ ∀ σ, (Prefix σ (ω.n) = ω) → σ ∉ P

/--
A minimal bad prefix is a bad prefix with no shorter bad prefix.
-/
def isMinimalBadPrefix {AP: Type} (P: LTProperty AP) (ω: FiniteWorld AP) : Prop := isBadPrefix P ω ∧ ∀ (m: ℕ) (h: m < ω.n), ¬ (isBadPrefix P (PrefixOfPrefix ω m (by
  rw [Nat.le_iff_lt_or_eq]
  left
  assumption
)))

/--
The set of all bad prefixes for a property.
-/
def BadPref {AP: Type} (P: LTProperty AP) : Set (FiniteWorld AP) := { ω | isBadPrefix P ω}

/--
The set of all minimal bad prefixes for a property.
-/
def MinBadPref {AP: Type} (P: LTProperty AP) : Set (FiniteWorld AP) := { ω | isMinimalBadPrefix P ω}

/--
A system satisfies a safety property iff no bad prefix is a finite trace of the system.
-/
theorem safety_satisfaction {AP: Type} (TSwts: TransitionSystemWTS AP) (P: LTProperty AP) (h: isSafetyProperty P) : TSwts ⊨ P ↔ ∀ ω ∈ BadPref P, ω ∉ TracesFin TSwts.TS := by
  have hTS := TSwts.h
  unfold hasNoTerminalStates at hTS
  constructor
  · intro h₁
    by_contra h₂
    simp only [not_forall, Classical.not_imp, not_not] at h₂
    obtain ⟨ω, hω⟩ := h₂
    obtain ⟨hω₁, hω₂⟩ := hω
    simp only [Satisfaction.Satisfies] at h₁
    unfold TracesWTS at h₁
    simp only [Set.mem_setOf_eq, Set.iUnion_subset_iff] at h₁
    unfold BadPref isBadPrefix at hω₁
    simp only [Set.mem_setOf_eq] at hω₁
    obtain ⟨_, hω₁⟩ := hω₁
    simp only [Membership.mem] at hω₂
    obtain ⟨s, hs⟩ := hω₂
    obtain ⟨hsi, hp⟩ := hs
    rw [Set.mem_def, Set.setOf_app_iff] at hsi
    unfold TracesFinFromState at hp
    simp only [Set.mem_image] at hp
    obtain ⟨π, hπ⟩ := hp
    obtain ⟨hπl, hπr⟩ := hπ
    let hinfπ := path_originates_from_state_if_noTerminalState hTS (π.states (Fin.last π.n))
    obtain ⟨πinf, hπinf⟩ := hinfπ

    match πinf with
    | PathFragment.finite p =>
      unfold PathsFromState at hπinf
      simp only [Set.mem_setOf_eq] at hπinf
      obtain ⟨hmax, _⟩ := hπinf
      unfold isMaximalPathFragment endStatePathFragment at hmax
      simp only at hmax
      specialize hTS (p.states (Fin.last p.n))
      contradiction
    | PathFragment.infinite p =>
      have hcont : π.states (Fin.last π.n) = p.states 0 := by
        unfold PathsFromState at hπinf
        simp only [Set.mem_setOf_eq] at hπinf
        obtain ⟨_, hstart⟩ := hπinf
        unfold startStatePathFragment at hstart
        simp only at hstart
        rw [hstart]
      let π' := PathFragment.concatenate_finite_and_infinite π p hcont

      let Trace := InfiniteTraceFromInfinitePathFragment π'
      let σ : World AP := Trace
      have hpref : Prefix σ ω.n = ω := by
        unfold Prefix
        obtain ⟨n, f⟩ := ω
        simp only [AbstractFiniteWorld.mk.injEq, heq_eq_eq, true_and]
        funext i
        unfold σ Trace InfiniteTraceFromInfinitePathFragment π' PathFragment.concatenate_finite_and_infinite
        simp only
        unfold FiniteTraceFromFinitePathFragment at hπr
        simp only [AbstractFiniteWorld.mk.injEq] at hπr
        obtain ⟨heq, hfeq⟩ := hπr
        rw [propext (Fin.heq_fun_iff (congrFun (congrArg HAdd.hAdd heq) 1))] at hfeq
        if c: i < n then
          have h': (i: ℕ) < π.n := by
            rw [heq]
            rw [@Fin.lt_iff_val_lt_val] at c
            simp only [Fin.natCast_eq_last, Fin.val_last] at c
            simp only [c]
          have h'' : (i: ℕ) < π.n + 1 := by
            apply Nat.lt_add_one_of_lt
            assumption
          simp only [h', ↓reduceIte]
          rw [hfeq]
          simp only [Fin.val_natCast, Nat.mod_eq_of_lt h'', Fin.eta]
        else
          simp only [Fin.natCast_eq_last, not_lt, Fin.last_le_iff] at c
          rw [c]
          simp only [Fin.val_last]
          simp only [heq, lt_self_iff_false, ↓reduceIte, tsub_self]
          specialize hfeq i
          simp only [c, Fin.val_last, Fin.val_natCast] at hfeq
          rw [← hcont, ← Fin.natCast_eq_last]
          simp only [heq]
          rw [hfeq]
          simp only [heq, Nat.mod_succ]
          unfold Fin.last
          simp only
      specialize hω₁ σ hpref
      specialize h₁ s hsi
      unfold TracesFromInitialStateWTS at h₁
      rw [Set.setOf_subset] at h₁
      simp only [forall_exists_index] at h₁

      specialize h₁ Trace (PathFragment.infinite π')
      have hpath : (PathFragment.infinite π') ∈ PathsFromState s := by
        unfold π' PathFragment.concatenate_finite_and_infinite PathsFromState isMaximalPathFragment endStatePathFragment startStatePathFragment
        simp only [Set.mem_setOf_eq, Nat.cast_zero, zero_le, Nat.sub_eq_zero_of_le, true_and]
        if c: 0 < π.n then
          simp only [c, ↓reduceIte]
          unfold PathsFinFromState startStatePathFragment at hπl
          simp only [Set.mem_setOf_eq] at hπl
          assumption
        else
          simp only [c, ↓reduceIte]
          simp only [not_lt, nonpos_iff_eq_zero] at c
          unfold PathsFinFromState startStatePathFragment at hπl
          simp only [Set.mem_setOf_eq] at hπl
          rw [← hcont, ← hπl]
          rw [← Fin.natCast_eq_last]
          simp only [c, Nat.cast_zero]

      specialize h₁ hpath
      have htr : Trace = TraceFromPathFromInitialStateWTS s (PathFragment.infinite π') hpath hsi := by
        unfold Trace TraceFromPathFromInitialStateWTS TraceFromPathWTS
        simp only

      rw [htr] at h₁
      simp only [forall_const] at h₁
      rw [← htr] at h₁
      unfold σ at hω₁
      contradiction
  · intro h₁
    by_contra h₂
    simp only [Satisfaction.Satisfies] at h₂
    unfold TracesWTS TracesFromInitialStateWTS at h₂
    simp only [Set.mem_setOf_eq, Set.iUnion_subset_iff, not_forall] at h₂
    obtain ⟨s, hs, h₂⟩ := h₂
    rw [Set.subset_def] at h₂
    simp only [Set.mem_setOf_eq, forall_exists_index, not_forall, Classical.not_imp,
      exists_and_right] at h₂
    obtain ⟨trace, π, hπpath, h₂⟩ := h₂
    obtain ⟨hπ, h₂⟩ := h₂

    let hsafe := h
    unfold isSafetyProperty at h
    specialize h trace
    apply h at h₂
    obtain ⟨nω, hbad⟩ := h₂
    let ω : FiniteWorld AP := ⟨nω, fun i => trace i⟩
    specialize h₁ ω
    unfold BadPref isBadPrefix at h₁
    simp only [hsafe, Set.mem_setOf_eq, ω] at h₁
    have h' : True ∧ ∀ (σ : World AP), Prefix σ ω.n = ω → σ ∉ P := by constructor <;> trivial
    apply h₁ at h'
    unfold TracesFin TracesFinFromState at h'
    simp only [Set.mem_setOf_eq, Set.mem_image, not_exists, not_and, ω] at h'
    simp only [Membership.mem, ω] at h'
    simp only [Set.Mem, ω] at h'
    specialize h' s hs

    match π with
    | PathFragment.finite p =>
      unfold PathsFromState isMaximalPathFragment endStatePathFragment at hπpath
      simp only [Set.mem_setOf_eq] at hπpath
      obtain ⟨hπl, hπr⟩ := hπpath
      specialize hTS (p.states (Fin.last p.n))
      contradiction
    | PathFragment.infinite p =>
      let πfin : FinitePathFragment TSwts.TS := ⟨nω, fun i => p.states i, by
      intro i
      have hv := p.valid i
      simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.coeSucc_eq_succ, Fin.val_succ]
      exact hv⟩
      specialize h' πfin

      have h₀ : PathsFinFromState s πfin := by
        unfold PathsFinFromState startStatePathFragment πfin
        rw [Set.setOf_app_iff]
        simp only [Fin.val_zero]
        unfold PathsFromState isMaximalPathFragment endStatePathFragment startStatePathFragment at hπpath
        simp only [Set.mem_setOf_eq, true_and] at hπpath
        assumption

      have h₀' : FiniteTraceFromFinitePathFragment πfin = { n := nω, f := ω.f } := by
        unfold FiniteTraceFromFinitePathFragment πfin ω
        simp only [Fin.val_natCast, Fin.coe_castSucc, Fin.val_succ, id_eq, eq_mpr_eq_cast,  AbstractFiniteWorld.mk.injEq, heq_eq_eq, true_and]
        funext i
        rw [hπ]
        unfold TraceFromPathFromInitialStateWTS TraceFromPathWTS InfiniteTraceFromInfinitePathFragment
        simp only

      apply h' at h₀
      apply h₀ at h₀'
      apply h₀'

/-!
## Prefixes and Closures

Defines the prefix and closure operators for LT properties and proves some of their properties.
-/
/--
The set of all prefixes of traces in an LT property.
-/
def prefLTProperty {AP: Type} (P: LTProperty AP) : Set (FiniteWorld AP) := ⋃ σ ∈ P, pref σ

/--
The closure of an LT property is the set of worlds whose prefixes are all prefixes of some world in the property.
-/
def closureLTProperty {AP: Type} (P: LTProperty AP) : Set (World AP) := {σ | pref σ ⊆ prefLTProperty P}

instance {AP: Type} : HasSubset (LTProperty AP) := ⟨fun P Q ↦ ∀ σ, σ ∈ P → σ ∈ Q⟩

instance {AP: Type} : Union (LTProperty AP) := ⟨fun P Q ↦ {σ | (σ ∈ P) ∨ (σ ∈ Q)}⟩

instance {AP: Type} : Inter (LTProperty AP) := ⟨fun P Q ↦ {σ | (σ ∈ P) ∧ (σ ∈ Q)}⟩

instance {AP: Type} : SDiff (LTProperty AP) := ⟨fun P Q ↦ {σ | (σ ∈ P) ∧ (σ ∉ Q)}⟩

/--
Every property is contained in its closure.
-/
theorem closure_contains_property {AP: Type} (P: LTProperty AP) : P ⊆ (closureLTProperty P) := by
  rw [Set.subset_def]
  intro σ hσ
  unfold closureLTProperty prefLTProperty
  rw [Set.mem_def, Set.setOf_app_iff]
  rw [Set.subset_def]
  intro ω hω
  rw [Set.mem_iUnion]
  use σ
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨hσ, hω⟩

/--
A property is a safety property iff it equals its closure.
-/
theorem safety_closure {AP: Type} (P: LTProperty AP) : isSafetyProperty P ↔ closureLTProperty P = P := by
  constructor
  · intro h₁
    rw [Set.Subset.antisymm_iff]
    constructor
    · rw [Set.subset_def]
      by_contra hc
      simp only [not_forall, Classical.not_imp] at hc
      obtain ⟨σ, hc⟩ := hc
      obtain ⟨hclos, hσ⟩ := hc
      unfold isSafetyProperty at h₁
      specialize h₁ σ hσ
      obtain ⟨n, h₁⟩ := h₁
      unfold closureLTProperty prefLTProperty at hclos
      rw [Set.mem_def, Set.setOf_app_iff] at hclos
      rw [Set.subset_def] at hclos
      specialize hclos (Prefix σ n) (by
        unfold pref
        rw [Set.mem_def]
        use n)
      simp only [Set.mem_iUnion, exists_prop] at hclos
      obtain ⟨σ', hσ'⟩ := hclos
      specialize h₁ σ'
      obtain ⟨hl, hr⟩ := hσ'
      unfold pref at hr
      rw [Set.mem_def] at hr
      obtain ⟨m, hr⟩ := hr
      have hnm : n = m := by
        unfold Prefix at hr
        simp only [AbstractFiniteWorld.mk.injEq] at hr
        obtain ⟨h', _⟩ := hr
        assumption
      rw [← hnm] at hr
      rw [Eq.symm hr] at h₁
      simp only [hr, forall_const] at h₁
      contradiction
    · apply closure_contains_property
  · intro h₁
    unfold isSafetyProperty
    intro σ hσ
    rw [← h₁] at hσ
    unfold closureLTProperty at hσ
    rw [Set.mem_def, Set.setOf_app_iff] at hσ
    unfold prefLTProperty at hσ
    rw [Set.not_subset_iff_exists_mem_not_mem] at hσ
    obtain ⟨ω, hω⟩ := hσ
    obtain ⟨hpref, hp⟩ := hω
    simp only [Set.mem_iUnion, exists_prop, not_exists, not_and] at hp
    unfold pref at hpref
    rw [Set.mem_def] at hpref
    obtain ⟨n, hpref⟩ := hpref
    use n
    intro σ' hσ'
    rw [← hpref] at hσ'
    by_contra hc
    specialize hp σ' hc
    unfold pref at hp
    rw [Set.mem_def] at hp
    simp only [not_exists] at hp
    specialize hp n
    rw [← hσ'] at hp
    contradiction

/--
The closure of the traces of a system is a safety property that the system satisfies.
-/
theorem closure_of_traces {AP: Type} (TSwts: TransitionSystemWTS AP) : isSafetyProperty (closureLTProperty (TracesWTS TSwts)) ∧ (TSwts ⊨ closureLTProperty (TracesWTS TSwts)) := by
  constructor
  · unfold isSafetyProperty
    intro σ hσ
    unfold closureLTProperty at hσ
    rw [Set.mem_def, Set.setOf_app_iff] at hσ
    unfold prefLTProperty at hσ
    rw [Set.subset_def] at hσ
    simp only [Set.mem_iUnion, exists_prop, not_forall, Classical.not_imp, not_exists, not_and] at hσ
    obtain ⟨ω, hω⟩ := hσ
    obtain ⟨hωl, hωr⟩ := hω
    unfold pref at hωl
    rw [Set.mem_def] at hωl
    obtain ⟨n, hωl⟩ := hωl
    use n
    rw [← hωl]
    intro σ' hσ'
    unfold closureLTProperty prefLTProperty
    rw [Set.mem_def, Set.setOf_app_iff, Set.subset_def]
    simp only [Set.mem_iUnion, exists_prop, not_forall, Classical.not_imp, not_exists, not_and]
    use ω
    constructor
    · unfold pref
      rw [Set.mem_def]
      use n
      rw [hσ']
    · assumption
  · simp only [Satisfaction.Satisfies]
    unfold closureLTProperty
    rw [Set.subset_def]
    intro σ hσ
    rw [Set.mem_def, Set.setOf_app_iff]
    unfold prefLTProperty
    rw [Set.subset_def]
    intro ω hω
    rw [Set.mem_iUnion]
    use σ
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨hσ, hω⟩

/--
Finite traces of a system are exactly the prefixes of its infinite traces.
-/
theorem finite_traces_are_prefixes {AP: Type} (TSwts: TransitionSystemWTS AP) : TracesFin TSwts.TS = prefLTProperty (TracesWTS TSwts) := by
  unfold prefLTProperty
  rw [Set.Subset.antisymm_iff, Set.subset_def, Set.subset_def]
  constructor
  · intro t ht
    unfold TracesFin at ht
    rw [Set.mem_def, Set.setOf_app_iff] at ht
    obtain ⟨s, hs, ht⟩ := ht
    simp only [Set.mem_setOf_eq] at hs
    unfold TracesFinFromState at ht
    simp only [Set.mem_image] at ht
    obtain ⟨πtail, hπ⟩ := ht
    obtain ⟨hπl, hπr⟩ := hπ
    simp only [Set.mem_iUnion, exists_prop]

    -- create a full path
    let hπhead := path_originates_from_state_if_noTerminalState TSwts.h (πtail.states (Fin.last πtail.n))
    obtain ⟨πhead, hπhead⟩ := hπhead
    match πhead with
    | PathFragment.finite p =>
      unfold PathsFromState at hπhead
      simp only [Set.mem_setOf_eq] at hπhead
      obtain ⟨hπheadmax, _⟩ := hπhead
      unfold isMaximalPathFragment endStatePathFragment at hπheadmax
      simp only at hπheadmax
      obtain ⟨_, hTS⟩ := TSwts
      specialize hTS (p.states (Fin.last p.n))
      contradiction
    | PathFragment.infinite p =>
      let π := PathFragment.concatenate_finite_and_infinite πtail p (by
        unfold PathsFromState startStatePathFragment at hπhead
        simp only [Set.mem_setOf_eq] at hπhead
        obtain ⟨hπheadl, hπheadr⟩ := hπhead
        rw [hπheadr]
      )
      have htrace : PathFragment.infinite π ∈ TSwts.TS.Paths := by
        unfold Paths isPath isInitialPathFragment isMaximalPathFragment endStatePathFragment startStatePathFragment
        simp only [Set.mem_setOf_eq, and_true]
        unfold π PathFragment.concatenate_finite_and_infinite
        simp only [Nat.cast_zero, zero_le, Nat.sub_eq_zero_of_le]
        if c: 0 < πtail.n then
          simp only [c, ↓reduceIte]
          unfold PathsFinFromState startStatePathFragment at hπl
          simp only [Set.mem_setOf_eq] at hπl
          rw [hπl]
          assumption
        else
          simp only [c, ↓reduceIte]
          simp only [not_lt, nonpos_iff_eq_zero] at c
          unfold PathsFinFromState startStatePathFragment at hπl
          simp only [Set.mem_setOf_eq] at hπl
          unfold PathsFromState startStatePathFragment at hπhead
          simp only [Set.mem_setOf_eq] at hπhead
          obtain ⟨_, hπhead⟩ := hπhead
          rw [hπhead]
          rw [← Fin.natCast_eq_last]
          simp only [c, Nat.cast_zero]
          rw [hπl]
          assumption
      let trace := TraceFromPathWTS (PathFragment.infinite π) htrace
      use trace
      constructor
      · unfold trace TracesWTS TracesFromInitialStateWTS TraceFromPathWTS
        rw [Set.mem_iUnion]
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        use s, hs
        use (PathFragment.infinite π)
        use (by
          unfold PathsFromState isMaximalPathFragment endStatePathFragment startStatePathFragment π
          unfold PathFragment.concatenate_finite_and_infinite
          simp only [Set.mem_setOf_eq, Nat.cast_zero, zero_le, Nat.sub_eq_zero_of_le, true_and]
          if c: 0 < πtail.n then
            simp only [c, ↓reduceIte]
            unfold PathsFinFromState startStatePathFragment at hπl
            simp only [Set.mem_setOf_eq] at hπl
            rw [hπl]
          else
            simp only [c, ↓reduceIte]
            simp only [not_lt, nonpos_iff_eq_zero] at c
            unfold PathsFinFromState startStatePathFragment at hπl
            simp only [Set.mem_setOf_eq] at hπl
            unfold PathsFromState startStatePathFragment at hπhead
            simp only [Set.mem_setOf_eq] at hπhead
            obtain ⟨_, hπhead⟩ := hπhead
            rw [hπhead]
            rw [← Fin.natCast_eq_last]
            simp only [c, Nat.cast_zero]
            rw [hπl])
        unfold TraceFromPathFromInitialStateWTS TraceFromPathWTS
        simp only
      · unfold pref
        rw [Set.mem_def]
        use t.n
        rw [← hπr]
        unfold FiniteTraceFromFinitePathFragment
        unfold Prefix
        simp only [AbstractFiniteWorld.mk.injEq, heq_eq_eq, true_and]
        funext i
        unfold trace π PathFragment.concatenate_finite_and_infinite TraceFromPathWTS InfiniteTraceFromInfinitePathFragment
        simp only [Fin.cast_val_eq_self]
        if c: ↑i < πtail.n then
          simp only [c, ↓reduceIte]
        else
          obtain ⟨i, hi⟩ := i
          simp only [c, ↓reduceIte]
          simp only [not_lt] at c
          have h': i ≤ πtail.n := by
            rw [Nat.le_iff_lt_add_one]
            assumption
          have heq : i = πtail.n := by apply Nat.le_antisymm <;> assumption
          simp only [heq, tsub_self]
          unfold PathsFromState startStatePathFragment at hπhead
          simp only [Set.mem_setOf_eq] at hπhead
          obtain ⟨_, hπhead⟩ := hπhead
          rw [hπhead]
          aesop

  · intro t ht
    unfold TracesFin TracesFinFromState
    simp only [Set.mem_setOf_eq, Set.mem_image]
    rw [Set.mem_iUnion] at ht
    obtain ⟨T, hT⟩ := ht
    rw [Set.mem_iUnion] at hT
    obtain ⟨hT₁, hT₂⟩ := hT
    unfold TracesWTS TracesFromInitialStateWTS at hT₁
    rw [Set.mem_iUnion] at hT₁
    simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hT₁
    obtain ⟨s, hs, hT₁⟩ := hT₁
    use s, hs
    obtain ⟨π, hπ, hT₁⟩ := hT₁
    unfold pref Prefix at hT₂
    rw [Set.mem_def] at hT₂
    unfold TraceFromPathFromInitialStateWTS TraceFromPathWTS at hT₁
    cases π with
    | finite p =>
      unfold PathsFromState isMaximalPathFragment endStatePathFragment at hπ
      simp only [Set.mem_setOf_eq] at hπ
      obtain ⟨hπ, _⟩ := hπ
      obtain ⟨_, hTS⟩ := TSwts
      specialize hTS (p.states (Fin.last p.n))
      contradiction
    | infinite p =>
      unfold InfiniteTraceFromInfinitePathFragment at hT₁
      simp only at hT₁
      rw [hT₁] at hT₂
      simp only at hT₂
      let πfin : FinitePathFragment TSwts.TS := ⟨t.n, fun i => p.states i, by
        intro i
        have hv := p.valid i
        simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.coeSucc_eq_succ, Fin.val_succ]
        exact hv⟩
      use πfin
      unfold PathsFinFromState startStatePathFragment
      simp only [Set.mem_setOf_eq]
      constructor
      · unfold πfin
        simp only [Fin.val_zero]
        unfold PathsFromState isMaximalPathFragment endStatePathFragment startStatePathFragment at hπ
        simp only [Set.mem_setOf_eq, true_and] at hπ
        assumption
      · unfold FiniteTraceFromFinitePathFragment πfin
        simp only [Fin.val_natCast, Fin.coe_castSucc, Fin.val_succ, id_eq, eq_mpr_eq_cast]
        obtain ⟨n, f⟩ := t
        simp only [AbstractFiniteWorld.mk.injEq, heq_eq_eq, true_and]
        simp only [AbstractFiniteWorld.mk.injEq, exists_eq_left', heq_eq_eq] at hT₂
        rw [hT₂]

/--
Prefixes of the closure of a property coincide with the prefixes of the property.
-/
theorem prefix_of_closure_is_prefix {AP: Type} (P : LTProperty AP) : prefLTProperty (closureLTProperty P) = prefLTProperty P := by
  rw [Set.Subset.antisymm_iff]
  constructor
  · unfold prefLTProperty
    rw [Set.subset_def]
    intro ω hω
    rw [Set.mem_iUnion] at hω
    obtain ⟨σ, hσ, hω⟩ := hω
    simp only [Set.mem_range, exists_prop] at hω
    rw [Set.mem_iUnion]
    simp only [Set.mem_iUnion, exists_prop]
    obtain ⟨hω₁, hω₂⟩ := hω
    obtain ⟨hω₁, hω₃⟩ := hω₁
    rw [← hω₃] at hω₂
    unfold closureLTProperty at hω₁
    rw [Set.mem_def, Set.setOf_app_iff] at hω₁
    unfold prefLTProperty at hω₁
    rw [Set.subset_def] at hω₁
    specialize hω₁ ω hω₂
    rw [Set.mem_iUnion] at hω₁
    simp only [Set.mem_iUnion, exists_prop] at hω₁
    obtain ⟨σ', hσ', hω₁⟩ := hω₁
    use σ'
  · unfold prefLTProperty
    rw [Set.subset_def]
    intro ω hω
    rw [Set.mem_iUnion] at hω
    obtain ⟨σ, hσ, hω⟩ := hω
    simp only [Set.mem_range, exists_prop] at hω
    rw [Set.mem_iUnion]
    simp only [Set.mem_iUnion, exists_prop]
    obtain ⟨hω₁, hω₂⟩ := hω
    obtain ⟨hω₁, hω₃⟩ := hω₁
    rw [← hω₃] at hω₂
    unfold closureLTProperty
    use σ
    rw [Set.mem_def, Set.setOf_app_iff]
    unfold prefLTProperty
    rw [Set.subset_def]
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro ω' hω'
      use σ
    · assumption

/--
Prefixes are monotonic with respect to set inclusion.
-/
theorem prefix_monotonicity {AP: Type} {P₁ P₂ : LTProperty AP} : P₁ ⊆ P₂ → prefLTProperty P₁ ⊆ prefLTProperty P₂ := by
  repeat rw [Set.subset_def]
  intro h
  intro ω hω
  unfold prefLTProperty at hω
  rw [Set.mem_iUnion] at hω
  simp only [Set.mem_iUnion, exists_prop] at hω
  obtain ⟨σ, hσ, hω⟩ := hω
  specialize h σ hσ
  unfold prefLTProperty
  rw [Set.mem_iUnion]
  simp only [Set.mem_iUnion, exists_prop]
  use σ

/--
Closure is monotonic with respect to set inclusion.
-/
theorem closure_monotonicity {AP: Type} {P₁ P₂ : LTProperty AP} : P₁ ⊆ P₂ → closureLTProperty P₁ ⊆ closureLTProperty P₂ := by
  intro h
  unfold closureLTProperty
  rw [Set.subset_def]
  simp only [Set.mem_setOf_eq]
  intro σ hσ
  rw [Set.subset_def]
  rw [Set.subset_def] at hσ
  have h' : prefLTProperty P₁ ⊆ prefLTProperty P₂ := by
    apply prefix_monotonicity
    assumption
  intro ω hω
  specialize hσ ω hω
  apply h'
  assumption

/--
Prefixes distribute over union.
-/
theorem prefix_distributes_over_union {AP: Type} (P Q: LTProperty AP) : prefLTProperty (P ∪ Q) = prefLTProperty P ∪ prefLTProperty Q := by
  rw [Set.Subset.antisymm_iff, Set.subset_def, Set.subset_def]
  constructor
  · intro σ hσ
    unfold prefLTProperty at hσ
    rw [Set.mem_iUnion] at hσ
    obtain ⟨σ', p, hσ⟩ := hσ
    simp only [Set.mem_range, exists_prop] at hσ
    rw [Set.union_def]
    unfold prefLTProperty
    simp only [Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]
    obtain ⟨hσ₁, hσ₂⟩ := hσ
    obtain ⟨hσ₁, hσ₃⟩ := hσ₁
    rw [← hσ₃] at hσ₂
    rw [Set.mem_union] at hσ₁
    cases hσ₁ with
    | inl hl =>
      left
      use σ'
    | inr hr =>
      right
      use σ'
  · have h₁ : P ⊆ P ∪ Q := by
      rw [Set.subset_def]
      intro σ hσ
      rw [Set.mem_union]
      left
      assumption
    have h₂ : Q ⊆ P ∪ Q := by
      rw [Set.subset_def]
      intro σ hσ
      rw [Set.mem_union]
      right
      assumption
    have h₁' := prefix_monotonicity h₁
    have h₂' := prefix_monotonicity h₂
    intro σ' hσ'
    rw [Set.mem_union] at hσ'
    cases hσ' with
    | inl _ =>
      apply h₁'
      assumption
    | inr _ =>
      apply h₂'
      assumption

/--
Closure distributes over union.
-/
theorem closure_distributes_over_union {AP: Type} (P Q: LTProperty AP) : closureLTProperty (P ∪ Q) = closureLTProperty P ∪ closureLTProperty Q := by
  rw [Set.Subset.antisymm_iff, Set.subset_def, Set.subset_def]
  constructor
  · intro σ hσ
    unfold closureLTProperty at hσ
    rw [Set.mem_def, Set.setOf_app_iff] at hσ
    rw [prefix_distributes_over_union] at hσ

    -- either pref(P) contains infinitely many prefixes of σ
    -- or pref(Q) contains infinitely many prefixes of σ
    have h : (∀ n, ∃ k > n, Prefix σ k ∈ prefLTProperty P) ∨ (∀ n, ∃ k > n, Prefix σ k ∈ prefLTProperty Q) := by
      by_contra hc
      simp only [LTLFormula.Or.or, gt_iff_lt, not_or, not_forall, not_exists, not_and] at hc
      obtain ⟨h₁, h₂⟩ := hc

      obtain ⟨n₁, h₁⟩ := h₁
      obtain ⟨n₂, h₂⟩ := h₂
      let n := n₁ + n₂ + 1
      have hn₁ : n₁ < n := by
        unfold n
        rw [Nat.lt_add_one_iff]
        simp only [le_add_iff_nonneg_right, zero_le]
      have hn₂ : n₂ < n := by
        unfold n
        rw [Nat.lt_add_one_iff]
        simp only [le_add_iff_nonneg_left, zero_le]
      specialize h₁ n hn₁
      specialize h₂ n hn₂

      rw [Set.subset_def] at hσ
      specialize hσ (Prefix σ n) (by
        unfold pref
        rw [Set.mem_def]
        use n)

      rw [Set.mem_union] at hσ
      cases hσ <;> contradiction

    have hyp (S: LTProperty AP) (hP: ∀ (n : ℕ), ∃ k > n, Prefix σ k ∈ prefLTProperty S) : pref σ ⊆ prefLTProperty S := by
      rw [Set.subset_def]
      by_contra hc
      simp only [not_forall, Classical.not_imp] at hc
      obtain ⟨ω, hω⟩ := hc
      obtain ⟨hω₁, hω₂⟩ := hω
      obtain ⟨n, f⟩ := ω

      specialize hP n
      obtain ⟨k, hk, hP⟩ := hP
      unfold prefLTProperty at hP
      rw [Set.mem_iUnion] at hP
      simp only [Set.mem_iUnion, exists_prop] at hP
      obtain ⟨σ', hσ', hP⟩ := hP

      unfold prefLTProperty at hω₂
      rw [Set.mem_iUnion] at hω₂
      simp only [Set.mem_iUnion, exists_prop, not_exists, not_and] at hω₂
      specialize hω₂ σ' hσ'
      unfold Prefix at hP

      apply hω₂
      unfold pref
      rw [Set.mem_def]
      use n
      unfold Prefix
      simp only [AbstractFiniteWorld.mk.injEq, heq_eq_eq, true_and]
      funext i
      unfold pref Prefix at hP
      rw [Set.mem_def] at hP
      simp only [AbstractFiniteWorld.mk.injEq, exists_eq_left', heq_eq_eq] at hP
      rw [funext_iff] at hP
      specialize hP i
      simp only [Fin.val_natCast] at hP
      rw [Nat.mod_eq_of_lt] at hP
      rw [← hP]

      unfold pref Prefix at hω₁
      rw [Set.mem_def] at hω₁
      simp only [AbstractFiniteWorld.mk.injEq, exists_eq_left', heq_eq_eq] at hω₁
      rw [funext_iff] at hω₁
      specialize hω₁ i
      exact hω₁

      simp only [gt_iff_lt] at hk
      rw [← Nat.add_one_lt_add_one_iff] at hk
      have h'' : ↑i < n + 1 → ↑i < k + 1 := by
        intro h
        have h''' := Nat.lt_trans h hk
        exact h'''

      apply h''
      simp only [Fin.is_lt]

    cases h with
    | inl hP =>
      rw [Set.mem_union]
      left
      let h' := hyp P hP
      unfold closureLTProperty
      simp only [Set.mem_setOf_eq]
      assumption
    | inr hQ =>
      rw [Set.mem_union]
      right
      let h' := hyp Q hQ
      unfold closureLTProperty
      simp only [Set.mem_setOf_eq]
      assumption
  · have h₁ : P ⊆ P ∪ Q := by
      rw [Set.subset_def]
      intro σ hσ
      rw [Set.mem_union]
      left
      assumption
    have h₂ : Q ⊆ P ∪ Q := by
      rw [Set.subset_def]
      intro σ hσ
      rw [Set.mem_union]
      right
      assumption
    have h₁' := closure_monotonicity h₁
    have h₂' := closure_monotonicity h₂
    intro σ hσ
    rw [Set.mem_union] at hσ
    cases hσ with
    | inl hσ' =>
      apply h₁'
      exact hσ'
    | inr hσ' =>
      apply h₂'
      exact hσ'

/--
Closure is idempotent, i.e., applying closure twice is the same as applying it once.
-/
theorem closure_idempotent {AP: Type} (P: LTProperty AP) : closureLTProperty (closureLTProperty P) = closureLTProperty P := by
  rw [Set.Subset.antisymm_iff, Set.subset_def, Set.subset_def]
  constructor
  · intro σ hσ
    unfold closureLTProperty at hσ
    rw [Set.mem_def, Set.setOf_app_iff] at hσ
    unfold closureLTProperty
    rw [Set.mem_def, Set.setOf_app_iff]
    rw [Set.subset_def] at hσ
    intro ω hω
    specialize hσ ω hω
    unfold prefLTProperty at hσ
    rw [Set.mem_iUnion] at hσ
    simp only [Set.mem_iUnion, exists_prop] at hσ
    unfold prefLTProperty
    rw [Set.mem_iUnion]
    simp only [Set.mem_iUnion, exists_prop]
    obtain ⟨σ', hσ', hω'⟩ := hσ
    rw [Set.mem_def, Set.setOf_app_iff, Set.subset_def] at hσ'
    specialize hσ' ω hω'
    rw [Set.mem_iUnion] at hσ'
    simp only [Set.mem_iUnion, exists_prop] at hσ'
    assumption
  · intro σ hσ
    apply closure_contains_property at hσ
    assumption

/-!
## Finite Trace Inclusion and Safety Properties

Finite trace inclusion between systems is equivalent to preservation of satisfaction for all safety properties.
-/
theorem safety_finite_trace_inclusion {AP: Type} (TSwts₁ TSwts₂ : TransitionSystemWTS AP) : (TracesFin TSwts₁.TS ⊆ TracesFin TSwts₂.TS) ↔ ∀ (P: LTProperty AP), isSafetyProperty P → (TSwts₂ ⊨ P → TSwts₁ ⊨ P) := by
  constructor
  · intro h₁
    intro P hPsafe h₂
    have h₃ := safety_satisfaction TSwts₂ P hPsafe
    have h₄ := safety_satisfaction TSwts₁ P hPsafe
    rw [h₃] at h₂
    rw [h₄]
    intro ω hω
    specialize h₂ ω hω
    by_contra hc
    rw [Set.subset_def] at h₁
    specialize h₁ (ω : FiniteTrace AP) hc
    contradiction
  · intro h₁
    have hclose := closure_of_traces TSwts₂
    obtain ⟨hclose₁, hclose₂⟩ := hclose
    specialize h₁ (closureLTProperty (TracesWTS TSwts₂)) hclose₁ hclose₂
    simp only [Satisfaction.Satisfies] at h₁
    have h₂ := finite_traces_are_prefixes TSwts₁
    have h₃ := finite_traces_are_prefixes TSwts₂
    have h₄ : prefLTProperty (TracesWTS TSwts₁) ⊆ prefLTProperty (closureLTProperty (TracesWTS TSwts₂)) := by
      rw [Set.subset_def]
      intro ω hω
      unfold prefLTProperty at hω
      rw [Set.mem_iUnion] at hω
      obtain ⟨σ, hσ, hω⟩ := hω
      simp only [Set.mem_range, exists_prop] at hω
      obtain ⟨hω₁, hω₃⟩ := hω
      obtain ⟨hω₁, hω₂⟩ := hω₁
      rw [← hω₂] at hω₃
      apply h₁ at hω₁
      unfold prefLTProperty
      rw [Set.mem_iUnion]
      use σ
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨hω₁, hω₃⟩
    have h₅ := prefix_of_closure_is_prefix (TracesWTS TSwts₂)

    rw [h₂, h₃]
    intro t
    intro ht
    apply h₄ at ht
    rw [← h₅]
    assumption

/--
Finite trace equivalence between systems is equivalent to satisfaction of all safety properties being equivalent.
-/
theorem safety_finite_trace_equivalence {AP: Type} (TSwts₁ TSwts₂ : TransitionSystemWTS AP) : (TracesFin TSwts₁.TS = TracesFin TSwts₂.TS) ↔ ∀ (P: LTProperty AP), isSafetyProperty P → (TSwts₁ ⊨ P ↔ TSwts₂ ⊨ P) := by
  rw [Set.Subset.antisymm_iff]
  repeat rw [safety_finite_trace_inclusion]
  constructor
  · intro h
    intro P hPsafe
    rw [iff_iff_implies_and_implies]
    obtain ⟨h₁, h₂⟩ := h
    specialize h₁ P hPsafe
    specialize h₂ P hPsafe
    constructor <;> assumption
  · intro h
    constructor <;> (
      intro P hPsafe
      specialize h P hPsafe
      rw [h]
      simp only [imp_self]
    )

/--
Structure used in the proof relating finite trace and trace inclusion.
-/
structure ftti_ProofStructure_0 {AP: Type} {TS : TransitionSystem AP} (n : ℕ) (t : InfiniteTrace AP) where
  f : (m : ℕ) → (Fin (m + 1))  → TS.S
  Iseq : Fin (n + 1) → Set ℕ
  Sseq : Fin (n + 1) → TS.S
  h₁: ∀ (k : Fin n), Iseq (k + 1) ⊆ Iseq k
  h₂: ∃ (p : FinitePathFragment TS), ((PathFragment.finite p) ∈ PathsFin TS) ∧ (p.n = n) ∧ (∀ i, p.states i = Sseq i)
  h₃: ∀ m ∈ Iseq n, ∀ (i : Fin (n + 1)), f m i = Sseq i
  h₄: TS.I (Sseq 0)
  h₅: ∀ (i : Fin (n + 1)), TS.L (Sseq i) = t i

structure ftti_ProofStructure_1 {α : Type} (n : ℕ) (f : α → ℕ) where
  s : Fin (n + 1) → α
  h : ∀ (k : Fin n), f (s k) < f (s (k + 1))

/--
Trace inclusion is equivalent to finite trace inclusion if the containing system is finite.
-/
theorem finite_trace_and_trace_inclusion {AP: Type} (TSwts : TransitionSystemWTS AP) (TS : TransitionSystem AP) (hfin : isFinite TS) : Traces TSwts.TS ⊆ Traces TS ↔ TracesFin TSwts.TS ⊆ TracesFin TS := by
  unfold isFinite at hfin
  constructor
  · intro h
    rw [finite_traces_are_prefixes]
    intro t ht
    unfold prefLTProperty at ht
    simp only [Set.mem_iUnion, exists_prop] at ht
    obtain ⟨T, hT₁, hT₂⟩ := ht
    let T' := Trace.infinite T
    unfold TracesWTS at hT₁
    rw [Set.mem_iUnion] at hT₁
    simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hT₁
    obtain ⟨s, hs, hT₁⟩ := hT₁
    have hT' : T' ∈ Traces TSwts.TS := by
      unfold Traces TracesFromState
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      use s, hs
      unfold TraceFromPathFragmentSet
      simp only [Set.mem_setOf_eq]
      unfold TracesFromInitialStateWTS at hT₁
      simp only [Set.mem_setOf_eq] at hT₁
      obtain ⟨π, hπ, hT₁⟩ := hT₁
      use π, hπ
      unfold T' TraceFromPathFragment
      match π with
      | PathFragment.finite p =>
        unfold PathsFromState isMaximalPathFragment endStatePathFragment at hπ
        simp only [Set.mem_setOf_eq] at hπ
        obtain ⟨hπ, _⟩ := hπ
        obtain ⟨_, hTS⟩ := TSwts
        specialize hTS (p.states (Fin.last p.n))
        contradiction
      | PathFragment.infinite p =>
        simp only [Trace.infinite.injEq]
        unfold TraceFromPathFromInitialStateWTS TraceFromPathWTS at hT₁
        simp only at hT₁
        assumption

    apply h at hT'
    unfold TracesFin TracesFinFromState
    simp only [Set.mem_setOf_eq, Set.mem_image]
    unfold Traces TracesFromState at hT'
    rw [Set.mem_iUnion] at hT'
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop] at hT'
    obtain ⟨s, hs, hT'⟩ := hT'
    use s, hs

    obtain ⟨π, hπ, hT'⟩ := hT'
    unfold PathsFinFromState
    simp only [Set.mem_setOf_eq]
    match π with
    | PathFragment.finite p =>
      unfold T' TraceFromPathFragment at hT'
      simp only [reduceCtorEq] at hT'
    | PathFragment.infinite p =>
      let πfin : FinitePathFragment TS := ⟨t.n, fun i => p.states i, by
        intro i
        have hv := p.valid i
        simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.coeSucc_eq_succ, Fin.val_succ]
        exact hv⟩
      use πfin
      unfold startStatePathFragment πfin
      simp only [Fin.val_zero]
      constructor
      · unfold PathsFromState isMaximalPathFragment endStatePathFragment startStatePathFragment at hπ
        simp only [Set.mem_setOf_eq, true_and] at hπ
        assumption
      · unfold FiniteTraceFromFinitePathFragment
        simp only [Fin.val_natCast, Fin.coe_castSucc, Fin.val_succ, id_eq, eq_mpr_eq_cast]
        unfold pref Prefix at hT₂
        rw [Set.mem_def] at hT₂
        obtain ⟨n, hT₂⟩ := hT₂
        unfold T' TraceFromPathFragment InfiniteTraceFromInfinitePathFragment at hT'
        simp only [Trace.infinite.injEq] at hT'
        rw [hT₂, hT']
  · intro h
    rw [Set.subset_def]
    intro t ht
    unfold Traces TracesFromState TraceFromPathFragmentSet PathsFromState at ht
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop] at ht
    obtain ⟨s, hs, ht⟩ := ht
    obtain ⟨π, hπ, ht⟩ := ht
    obtain ⟨hπmax, hπstart⟩ := hπ
    unfold isMaximalPathFragment endStatePathFragment at hπmax
    cases π with
    | finite p =>
      simp only at hπmax
      have hTS := TSwts.h
      unfold hasNoTerminalStates at hTS
      specialize hTS (p.states (Fin.last p.n))
      contradiction
    | infinite p =>
      simp only at hπmax
      let T := InfiniteTraceFromInfinitePathFragment p

      have hpref : ∀ q ∈ (pref T), ↑q ∈ TracesFin TS := by
        intro q hq
        apply h
        rw [finite_traces_are_prefixes]
        unfold prefLTProperty
        simp only [Set.mem_iUnion, exists_prop]
        use T
        constructor
        · unfold TracesWTS TracesFromInitialStateWTS
          rw [Set.mem_iUnion]
          simp only [Set.mem_setOf_eq, Set.mem_iUnion]
          use s, hs
          use (PathFragment.infinite p)
          unfold PathsFromState isMaximalPathFragment endStatePathFragment
          simp only [Set.mem_setOf_eq, true_and]
          use hπstart
          unfold TraceFromPathFromInitialStateWTS TraceFromPathWTS
          simp only
          unfold T
          rfl
        · simp only [hq]

      let finPath (m: ℕ) : FinitePathFragment TS := by
        have mpref : ∃ q ∈ (pref T), (↑q ∈ TracesFin TS) ∧ (q.n = m) := by
          let q : FiniteWorld AP := Prefix T m
          have hq : q ∈ pref T := by
            unfold pref
            rw [Set.mem_def]
            use m
          specialize hpref q
          use q
          use hq
          apply hpref at hq
          use hq
          unfold q Prefix
          simp only

        let hq := mpref.choose_spec
        let q := mpref.choose
        obtain ⟨hq₁, hq₂, hq₃⟩ := hq

        unfold TracesFin TracesFinFromState at hq₂
        simp only [Set.mem_setOf_eq, Set.mem_image] at hq₂
        let hq₂' := hq₂.choose_spec
        obtain ⟨hq₂₁, hq₂₂⟩ := hq₂'
        let path := hq₂₂.choose
        let hpath := hq₂₂.choose_spec

        exact path

      let finPathState m n : TS.S := (finPath m).states n

      let proofStructure (n : ℕ) : ftti_ProofStructure_0 n T :=
        match n with
        | 0 => by
          have hm : ∃ m, ∀ k, ∃ j > k, (finPathState m 0) = (finPathState j 0) := by
            by_contra hc
            simp only [gt_iff_lt, not_exists, not_forall, not_and] at hc
            obtain ⟨hfin, _, _⟩ := hfin

            let getLimit : ℕ → ℕ := fun n => by
              specialize hc n
              let lim := hc.choose
              let hlim := hc.choose_spec
              exact lim

            let getLimitFromState : TS.S → ℕ := fun s => by
              if hs: ∃ m, s = finPathState m 0 then
                let m := hs.choose
                exact getLimit m
              else
                exact 0

            have hmax : ∃ n, ∀ (s: TS.S), n ≥ getLimitFromState s := by
              by_contra hmaxc
              simp only [ge_iff_le, not_exists, not_forall, not_le] at hmaxc

              let proofStructure_1 (n : ℕ) : ftti_ProofStructure_1 n getLimitFromState := by
                induction n with
                | zero =>
                  exact ⟨
                    by
                      specialize hmaxc 0
                      let s := hmaxc.choose
                      exact (fun n ↦ s),
                    by simp⟩
                | succ k prev =>
                  obtain ⟨prevs, prevh⟩ := prev
                  let ps := prevs k
                  specialize hmaxc (getLimitFromState ps)
                  let ns := hmaxc.choose
                  exact ⟨
                    fun m ↦ if m < k + 1 then prevs m else ns,
                    by
                      intro i
                      if c : i < k then
                        have hi : i.succ < k + 1 := sorry
                        have hi' : i.castSucc < k + 1 := sorry
                        simp only [Fin.coe_eq_castSucc, hi', ↓reduceIte, Fin.coe_castSucc,
                          Fin.cast_val_eq_self, Fin.coeSucc_eq_succ, hi, Fin.val_succ, Nat.cast_add,
                          Nat.cast_one, gt_iff_lt]
                        specialize prevh (Fin.mk i (by sorry))
                        simp at prevh
                        assumption
                      else
                        simp at c
                        have hi : ↑k < Fin.last (k + 1) := sorry
                        simp only [c, Fin.val_last, Fin.lt_add_one_iff, hi, ↓reduceIte,
                          Fin.val_natCast, lt_self_iff_false, gt_iff_lt]
                        rw [Nat.mod_eq_of_lt (by sorry)]
                        unfold ns
                        have hns := hmaxc.choose_spec
                        unfold ps at hns
                        assumption⟩

              let f (n : ℕ) : TS.S := (proofStructure_1 n).s n

              have hfinc' (a : ℕ) : getLimitFromState (f a) < getLimitFromState (f (a + 1)) := by
                have hf := (proofStructure_1 (a + 1)).h a
                unfold f
                simp only [Fin.natCast_eq_last, Fin.val_last] at hf
                have ha : (proofStructure_1 (a + 1)).s ↑a = (proofStructure_1 a).s ↑a := by


                  sorry
                rw [ha] at hf
                rw [← @Nat.cast_add_one] at hf
                assumption

              have hfinc (a b : ℕ) : a < b → getLimitFromState (f a) < getLimitFromState (f b) := by
                induction b with
                | zero => simp
                | succ k ih =>
                  have hk := hfinc' k
                  intro hk'
                  if c : a < k then
                    apply ih at c
                    apply Nat.lt_trans c hk
                  else
                    simp at c
                    rw [Nat.lt_add_one_iff] at hk'
                    have hk'' : a = k := by
                      rw [Nat.eq_iff_le_and_ge]
                      constructor <;> assumption
                    rw [hk'']
                    assumption

              have hf := not_injective_infinite_finite f
              rw [Function.not_injective_iff] at hf
              obtain ⟨a, b, hf, hab⟩ := hf
              rw [Nat.ne_iff_lt_or_gt] at hab
              cases hab with
              | _ hab =>
                apply hfinc at hab
                rw [hf] at hab
                simp at hab

            obtain ⟨max, hmax⟩ := hmax
            specialize hc (max + 1)
            sorry

          let m := hm.choose
          let hm' := hm.choose_spec
          let s₀ := finPathState m 0
          let I := {j | s₀ = finPathState j 0}

          exact ⟨
            by
              sorry,
            fun k => I,
            fun k => s₀,
            by simp only [subset_refl, implies_true],
            by
              sorry,
            by
              sorry,
            by
              sorry,
            by
              sorry⟩
        | k + 1 => sorry

      let π : InfinitePathFragment TS := ⟨fun i => (proofStructure i).Sseq i, by
          intro i
          simp only [Fin.natCast_eq_last, Nat.cast_add, Nat.cast_one]
          sorry⟩

      unfold Traces TracesFromState TraceFromPathFragmentSet
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      use (π.states 0)
      constructor
      · unfold π
        simp only [Nat.reduceAdd, Nat.cast_zero, Fin.isValue]
        apply (proofStructure 0).h₄
      · use (PathFragment.infinite π)
        constructor
        · have hstart := path_starts_from_startState (PathFragment.infinite π) (by sorry)
          unfold startStatePathFragment at hstart
          simp only at hstart
          assumption
        · unfold TraceFromPathFragment InfiniteTraceFromInfinitePathFragment
          simp only
          match t with
          | Trace.finite t' =>
            unfold TraceFromPathFragment InfiniteTraceFromInfinitePathFragment at ht
            simp at ht
          | Trace.infinite t' =>
            simp only [Trace.infinite.injEq]
            funext i
            have hT := (proofStructure i).h₅
            unfold π
            simp only [Fin.natCast_eq_last]
            specialize hT i
            unfold TraceFromPathFragment InfiniteTraceFromInfinitePathFragment at ht
            simp only [Trace.infinite.injEq] at ht
            rw [ht]
            simp only
            simp only [Fin.natCast_eq_last, Fin.val_last] at hT
            rw [hT]
            unfold T InfiniteTraceFromInfinitePathFragment
            rfl


/-!
## Liveness Properties

A property is a liveness property if every finite word is a prefix of some world in the property.
-/
def isLivenessProperty {AP: Type} (P: LTProperty AP) : Prop := prefLTProperty P = {ω | ω : FiniteWorld AP}

/--
The only LT property that is both a safety and a liveness property is the trivial property.
-/
theorem intersection_safety_liveness {AP: Type} (P: LTProperty AP) : isSafetyProperty P ∧ isLivenessProperty P → P = {σ | σ : World AP} := by
  intro h
  obtain ⟨hsafe, hlive⟩ := h
  unfold isLivenessProperty at hlive
  rw [safety_closure] at hsafe
  rw [← hsafe]
  unfold closureLTProperty
  rw [hlive]
  simp only [exists_eq, Set.setOf_true, Set.subset_univ]

/--
Any LT property can be decomposed into a safety and a liveness property.
-/
theorem decomposition {AP: Type} (P: LTProperty AP) : ∃ (Psafe Plive : LTProperty AP), isSafetyProperty Psafe ∧ isLivenessProperty Plive ∧ P = Psafe ∩ Plive := by
  have h₁ : P = (closureLTProperty P) ∩ P := by
    rw [Set.Subset.antisymm_iff]
    constructor
    · rw [Set.subset_def]
      intro σ hσ
      rw [Set.mem_inter_iff]
      constructor
      · apply closure_contains_property at hσ
        assumption
      · assumption
    · rw [Set.subset_def]
      intro σ hσ
      rw [Set.mem_inter_iff] at hσ
      obtain ⟨hσ₁, hσ₂⟩ := hσ
      assumption

  have hsafe : isSafetyProperty (closureLTProperty P) := by
    rw [safety_closure, closure_idempotent]

  have h₂ : P = (closureLTProperty P) ∩ (P ∪ ({σ | σ : World AP} \ closureLTProperty P)) := by
    rw [Set.Subset.antisymm_iff, Set.subset_def, Set.subset_def]
    constructor
    · intro σ hσ
      rw [Set.mem_inter_iff]
      constructor
      · rw [h₁] at hσ
        rw [Set.mem_inter_iff] at hσ
        obtain ⟨hσ₁, hσ₂⟩ := hσ
        assumption
      · rw [Set.mem_union]
        left
        assumption
    · intro σ hσ
      rw [Set.mem_inter_iff] at hσ
      obtain ⟨hσ₁, hσ₂⟩ := hσ
      rw [h₁]
      rw [Set.mem_inter_iff]
      simp only [hσ₁, true_and]
      rw [Set.mem_union] at hσ₂
      cases hσ₂ with
      | inl hl => assumption
      | inr hr =>
        rw [Set.mem_diff] at hr
        obtain ⟨_, hr⟩ := hr
        contradiction

  let Plive := (P ∪ ({σ | σ : World AP} \ closureLTProperty P))

  have hlive : isLivenessProperty Plive := by
    unfold isLivenessProperty

    have hcl : closureLTProperty Plive = {ω | ω : World AP} := by
      unfold Plive
      rw [closure_distributes_over_union]
      rw [Set.Subset.antisymm_iff, Set.subset_def, Set.subset_def]
      simp only [exists_eq, Set.setOf_true, Set.mem_union, Set.mem_univ, implies_true, forall_const, true_and]
      intro σ
      if hσ: σ ∈ closureLTProperty P then
        left
        assumption
      else
        right
        apply closure_contains_property
        rw [Set.mem_diff]
        simp only [Set.mem_univ, true_and]
        assumption

    unfold closureLTProperty at hcl
    rw [Set.Subset.antisymm_iff, Set.subset_def, Set.subset_def] at hcl
    simp only [Set.mem_setOf_eq, exists_eq, Set.setOf_true, Set.mem_univ, implies_true, forall_const,  true_and] at hcl
    rw [Set.Subset.antisymm_iff, Set.subset_def, Set.subset_def]
    simp only [exists_eq, Set.setOf_true, Set.mem_univ, implies_true, forall_const, true_and]
    intro ω

    let σ : World AP := fun i => if i < ω.n + 1 then ω.f i else ω.f (ω.n - 1)
    specialize hcl σ
    apply hcl
    unfold pref
    rw [Set.mem_def]
    use ω.n
    unfold Prefix
    obtain ⟨n, f⟩ := ω
    simp only [AbstractFiniteWorld.mk.injEq, heq_eq_eq, true_and]
    funext i
    unfold σ
    simp only [Fin.is_lt, ↓reduceIte, Fin.cast_val_eq_self]

  use closureLTProperty P, Plive, hsafe, hlive

/--
The above decomposition is the sharpest possible.
-/
theorem sharpest_decomposition {AP: Type} (P: LTProperty AP) : ∀ (Psafe Plive : LTProperty AP), isSafetyProperty Psafe ∧ isLivenessProperty Plive ∧ P = Psafe ∩ Plive → (closureLTProperty P ⊆ Psafe) ∧ Plive ⊆ P ∪ ({σ | σ : World AP} \ closureLTProperty P) := by
  intro Psafe Plive h
  obtain ⟨hsafe, hlive, h⟩ := h
  constructor
  · rw [Set.subset_def]
    intro σ hσ
    unfold isSafetyProperty at hsafe
    unfold closureLTProperty prefLTProperty at hσ
    rw [Set.mem_def, Set.setOf_app_iff, Set.subset_def] at hσ
    by_contra hc
    specialize hsafe σ hc
    obtain ⟨n, hsafe⟩ := hsafe
    specialize hσ (Prefix σ n) (by
      unfold pref
      rw [Set.mem_def]
      use n)
    rw [Set.mem_iUnion] at hσ
    simp only [Set.mem_iUnion, exists_prop] at hσ
    obtain ⟨σ', hσ', hσ⟩ := hσ
    rw [h] at hσ'
    rw [Set.mem_inter_iff] at hσ'
    obtain ⟨hσ', _⟩ := hσ'
    specialize hsafe σ'
    apply hsafe
    unfold pref at hσ
    rw [Set.mem_def] at hσ
    obtain ⟨n', hσ⟩ := hσ
    rw [hσ]
    unfold Prefix
    simp only [AbstractFiniteWorld.mk.injEq]
    unfold Prefix at hσ
    simp only [AbstractFiniteWorld.mk.injEq] at hσ
    obtain ⟨hσ₁, hσ₂⟩ := hσ
    simp only [hσ₁, true_and]
    rw [hσ₁]
    assumption
  · unfold isLivenessProperty at hlive
    rw [Set.subset_def]
    intro σ hσ
    if hp: σ ∈ P then
      left
      assumption
    else
      right
      rw [Set.mem_diff]
      simp only [exists_eq, Set.setOf_true, Set.mem_univ, true_and]
      unfold closureLTProperty prefLTProperty
      rw [Set.mem_def, Set.setOf_app_iff, Set.subset_def]
      simp only [Set.mem_iUnion, exists_prop, not_forall, Classical.not_imp, not_exists, not_and]
      rw [h, Set.mem_inter_iff] at hp
      simp only [not_and] at hp
      simp only [hσ, not_true_eq_false, imp_false] at hp
      unfold isSafetyProperty at hsafe
      specialize hsafe σ hp
      obtain ⟨n, hsafe⟩ := hsafe
      use (Prefix σ n)
      constructor
      · unfold pref
        rw [Set.mem_def]
        use n
      · intro σ' hσ'
        unfold pref Prefix
        rw [Set.mem_def]
        simp only [AbstractFiniteWorld.mk.injEq, exists_eq_left', heq_eq_eq]
        rw [funext_iff]
        by_contra hc
        specialize hsafe σ'

        have h' : Prefix σ' n = Prefix σ n := by
          unfold Prefix
          simp only [AbstractFiniteWorld.mk.injEq, heq_eq_eq, true_and]
          funext i
          specialize hc i
          simp only [hc]

        apply hsafe at h'
        rw [h, Set.mem_inter_iff] at hσ'
        obtain ⟨hσ₁, hσ₂⟩ := hσ'
        contradiction

end section
