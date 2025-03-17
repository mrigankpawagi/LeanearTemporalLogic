import Mathlib
import LeanearTemporalLogic.LTL
import LeanearTemporalLogic.TransitionSystems
import LeanearTemporalLogic.LTProperty

/-!
We will define a satisfaction relation as a type class. This will allow us to define satisfaction for different types of models.
-/
class Satisfaction (α : Type u) (β : Type v) where
  Satisfies : α → β → Prop

infixl:70 (priority := high) " ⊨ " => Satisfaction.Satisfies

class Equivalent (α : Type) where
  Equiv : α → α → Prop

infixl:70 (priority := high) " ≡ " => Equivalent.Equiv

/-!
A world is a sequence of states where each state is set of atomic propositions (that are considered true in that state).
-/
def World (AP: Type) : Type := ℕ → Set AP

/-!
A suffix of a world w starting at index i is a world w' such that w'(j) = w(i+j) for all j. We will denote this by w[i...].
-/
def suffix {AP: Type} (σ : World AP) (i : ℕ) : World AP := fun j => σ (i + j)

syntax:60 term "[" term "…]" : term
macro_rules
  | `($σ[$i…]) => `(suffix $σ $i)

/-!
A simple lemma for composition of suffixes.
-/
theorem suffix_composition {AP: Type} (σ : World AP) (i j : ℕ) : σ[i…][j…] = σ[i+j…] := by
  funext k
  unfold suffix
  rw [Nat.add_assoc]

theorem suffix_zero_identity {AP: Type} (σ : World AP) : σ[0…] = σ := by
  funext k
  unfold suffix
  rw [Nat.zero_add]

/-!
Now we define what it means for a world to satisfy an LTL formula.
-/
section
open LTLFormula

def world_satisfies_ltl {AP: Type} (σ : World AP) : LTLFormula AP → Prop
  | ⊤ => true
  | LTLFormula.atom a => a ∈ σ 0
  | ¬ ψ => ¬ (world_satisfies_ltl σ ψ)
  | ϕ₁ ∧ ϕ₂ => (world_satisfies_ltl σ ϕ₁) ∧ (world_satisfies_ltl σ ϕ₂)
  | ◯ ψ => world_satisfies_ltl (σ[1…]) ψ
  | ϕ₁ 𝓤 ϕ₂ => ∃ (j: ℕ), ((world_satisfies_ltl (σ[j…]) ϕ₂) ∧ ∀ (k: ℕ), (k < j → world_satisfies_ltl (σ[k…]) ϕ₁))

instance {AP: Type} : Satisfaction (World AP) (LTLFormula AP) := ⟨world_satisfies_ltl⟩

/-!
We will also define satisfaction of an LTL formula by a single state, which is the same as satisfaction by a world with that state as the first state and all other states empty.
-/
instance {AP: Type} : Satisfaction (Set AP) (LTLFormula AP) := ⟨fun A ϕ => by
  let f : World AP := fun n => if n = 0 then A else ∅
  exact f ⊨ ϕ⟩

/-!
We will also define some useful lemmas for satisfaction.
-/
def world_satisfies_negation {AP: Type} (σ : World AP) (ϕ : LTLFormula AP) : (σ ⊨ (¬ ϕ)) ↔ (¬ (σ ⊨ ϕ)) := by
  simp [Satisfaction.Satisfies]
  rw [world_satisfies_ltl]

def world_satisfies_or {AP: Type} (σ : World AP) (ϕ₁ ϕ₂ : LTLFormula AP) : (σ ⊨ (ϕ₁ ∨ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∨ (σ ⊨ ϕ₂)) := by
  simp [Satisfaction.Satisfies]
  repeat rw [world_satisfies_ltl]
  simp [Or.or, Not.not]
  constructor
  · intro h
    contrapose h
    simp at h
    simp
    assumption
  · intro h
    contrapose h
    simp at h
    simp
    assumption

def world_satisfies_next {AP: Type} (σ : World AP) (ϕ : LTLFormula AP) : (σ ⊨ (◯ ϕ)) ↔ ((σ[1…]) ⊨ ϕ) := by
  simp [Satisfaction.Satisfies]
  rw [world_satisfies_ltl]

def world_satisfies_and {AP: Type} (σ : World AP) (ϕ₁ ϕ₂ : LTLFormula AP) : (σ ⊨ (ϕ₁ ∧ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∧ (σ ⊨ ϕ₂)) := by
  simp [Satisfaction.Satisfies]
  repeat rw [world_satisfies_ltl]

def world_satisfies_until {AP: Type} (σ : World AP) (ϕ₁ ϕ₂ : LTLFormula AP) : (σ ⊨ (ϕ₁ 𝓤 ϕ₂)) ↔ ∃ (j: ℕ), (((σ[j…]) ⊨ ϕ₂) ∧ ∀ (k: ℕ), (k < j → ((σ[k…]) ⊨ ϕ₁))) := by
  simp [Satisfaction.Satisfies]
  rw [world_satisfies_ltl]

/-!
We will now show satisfaction for ♢ and □ operators.
-/
theorem world_satisfies_eventually {AP: Type} (σ : World AP) (ϕ : LTLFormula AP) : (σ ⊨ (♢ ϕ)) ↔ ∃ (i: ℕ), ((σ[i…]) ⊨ ϕ) := by
  unfold eventually
  simp [Satisfaction.Satisfies]
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

theorem world_satisfies_always {AP: Type} (σ : World AP) (ϕ : LTLFormula AP) : (σ ⊨ (□ ϕ)) ↔ ∀ (i: ℕ), ((σ[i…]) ⊨ ϕ) := by
  unfold always

  constructor
  -- left to right
  · intro h
    intro i
    simp [Satisfaction.Satisfies] at h
    rw [world_satisfies_ltl] at h
    have h₁ := world_satisfies_eventually σ (¬ ϕ)
    simp [Satisfaction.Satisfies] at h₁
    rw [h₁] at h
    simp [Not.not] at h
    specialize h i
    rw [world_satisfies_ltl] at h
    simp [Not.not] at h
    simp [Satisfaction.Satisfies]
    assumption

  -- right to left
  · intro h
    simp [Satisfaction.Satisfies]
    rw [world_satisfies_ltl]
    simp [Not.not]
    have h₁ := world_satisfies_eventually σ (¬ ϕ)
    simp [Satisfaction.Satisfies] at h₁
    rw [h₁]
    simp
    intro i
    rw [world_satisfies_ltl]
    simp [Not.not]
    simp [Satisfaction.Satisfies] at h
    apply h

theorem world_satisfies_always_eventually {AP: Type} (σ : World AP) (ϕ : LTLFormula AP) : (σ ⊨ (□ ♢ ϕ)) ↔ ∀ (i: ℕ), ∃ (j: ℕ), ((σ[i+j…]) ⊨ ϕ) := by
  constructor

  -- left to right
  · intro h
    intro i
    rw [world_satisfies_always] at h
    specialize h i
    rw [world_satisfies_eventually] at h
    obtain ⟨j, hj⟩ := h
    rw [suffix_composition] at hj
    use j

  -- right to left
  · intro h
    rw [world_satisfies_always]
    intro i
    rw [world_satisfies_eventually]
    specialize h i
    obtain ⟨j, hj⟩ := h
    use j
    rw [suffix_composition]
    assumption

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
    rw [suffix_composition] at hi
    assumption

  -- right to left
  · intro h
    rw [world_satisfies_eventually]
    obtain ⟨i, hi⟩ := h
    use i
    rw [world_satisfies_always]
    intro j
    specialize hi j
    rw [suffix_composition]
    assumption


/-!
We now define the set of worlds that satisfy a given LTL formula.
-/
def Worlds {AP: Type} (ϕ : LTLFormula AP) : Set (World AP) := fun σ => σ ⊨ ϕ

/-!
We will now define the notion of equivalence of LTL formulae.
-/
instance {AP: Type} : Equivalent (LTLFormula AP) := ⟨fun ϕ ψ => Worlds ϕ = Worlds ψ⟩

/-!
It will be useful to show that this is an equivalence relation.
-/
theorem equivalent_ltl_refl {AP: Type} (ϕ : LTLFormula AP) : ϕ ≡ ϕ := by
  simp [Equivalent.Equiv]

theorem equivalent_ltl_symm {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ ≡ ψ) → (ψ ≡ ϕ) := by
  simp [Equivalent.Equiv]
  intro h
  rw [h]

theorem equivalent_ltl_trans {AP: Type} (ϕ ψ χ : LTLFormula AP) : (ϕ ≡ ψ) → (ψ ≡ χ) → (ϕ ≡ χ) := by
  simp [Equivalent.Equiv]
  intro h₁ h₂
  rw [h₁]
  exact h₂

/-!
It would also be useful to show that equivalence is preserved by certain operations.
-/
theorem equivalent_ltl_preserves_negation {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ ≡ ψ) ↔ ((¬ ϕ) ≡ (¬ ψ)) := by
  simp [Equivalent.Equiv]
  constructor
  · intro h
    funext σ
    have h₁ : Worlds ϕ σ = Worlds ψ σ := by rw [h]
    simp [Worlds] at h₁
    simp [Worlds]
    simp [Satisfaction.Satisfies]
    rw [world_satisfies_ltl, world_satisfies_ltl]
    simp [Not.not]
    simp [Satisfaction.Satisfies] at h₁
    rw [h₁]
  · intro h
    funext σ
    have h₁ : Worlds (¬ ϕ) σ = Worlds (¬ ψ) σ := by
      simp [Worlds]
      rw [← Worlds, ← Worlds]
      rw [h]
    simp [Worlds] at h₁
    simp [Worlds]
    simp [Satisfaction.Satisfies]
    simp [Satisfaction.Satisfies] at h₁
    rw [world_satisfies_ltl, world_satisfies_ltl] at h₁
    simp [Not.not] at h₁
    constructor
    · intro h'
      contrapose h'
      rw [h₁]
      assumption
    · intro h'
      contrapose h'
      rw [← h₁]
      assumption

theorem equivalent_ltl_preserves_always {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ ≡ ψ) → ((□ ϕ) ≡ (□ ψ)) := by
  simp [Equivalent.Equiv]
  intro h
  funext σ
  unfold Worlds
  rw [world_satisfies_always, world_satisfies_always]
  simp
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

/-!
Now we prove some equivalence rules for LTL formulae.
-/

theorem ltl_double_negation {AP: Type} (ϕ : LTLFormula AP) : (¬ (¬ ϕ)) ≡ ϕ := by
  simp [Equivalent.Equiv]
  funext σ
  simp [Worlds]
  constructor
  · intro h
    simp [Satisfaction.Satisfies] at h
    rw [world_satisfies_ltl, world_satisfies_ltl] at h
    simp [Not.not] at h
    simp [Satisfaction.Satisfies]
    assumption
  · intro h
    simp [Satisfaction.Satisfies]
    rw [world_satisfies_ltl, world_satisfies_ltl]
    simp [Not.not]
    assumption

theorem ltl_duality_next {AP: Type} (ϕ : LTLFormula AP) : ((¬ (◯ ϕ)) ≡ (◯ (¬ ϕ))) := by
  simp [Equivalent.Equiv]
  funext σ
  simp [Worlds]
  constructor

  -- left to right
  · intro h
    simp [Satisfaction.Satisfies] at h
    rw [world_satisfies_ltl, world_satisfies_ltl] at h
    simp [Satisfaction.Satisfies]
    rw [world_satisfies_ltl, world_satisfies_ltl]
    assumption

  -- right to left
  · intro h
    simp [Satisfaction.Satisfies] at h
    rw [world_satisfies_ltl, world_satisfies_ltl] at h
    simp [Satisfaction.Satisfies]
    rw [world_satisfies_ltl, world_satisfies_ltl]
    assumption

theorem ltl_duality_eventually {AP: Type} (ϕ : LTLFormula AP) : ((¬ (♢ ϕ)) ≡ (□ (¬ ϕ))) := by
  simp [Equivalent.Equiv]
  funext σ
  simp [Worlds]
  constructor

  -- left to right
  · intro h
    simp [Satisfaction.Satisfies] at h
    rw [world_satisfies_ltl] at h
    have h₁ : ¬ (σ ⊨ (♢ ϕ)) := by
      simp [Satisfaction.Satisfies]
      assumption
    rw [world_satisfies_eventually] at h₁
    simp [Not.not] at h₁
    rw [world_satisfies_always]
    intro i
    simp [Satisfaction.Satisfies]
    rw [world_satisfies_ltl]
    specialize h₁ i
    simp [Satisfaction.Satisfies] at h₁
    apply h₁

  -- right to left
  · intro h
    simp [Satisfaction.Satisfies]
    rw [world_satisfies_ltl]
    have h₁ : ¬ (σ ⊨ (♢ ϕ)) := by
      rw [world_satisfies_eventually]
      simp [Not.not]
      intro i
      simp [Satisfaction.Satisfies]
      rw [world_satisfies_always] at h
      specialize h i
      simp [Satisfaction.Satisfies] at h
      rw [world_satisfies_ltl] at h
      apply h
    simp [Satisfaction.Satisfies] at h₁
    apply h₁

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

theorem ltl_idempotence_eventually {AP: Type} (ϕ : LTLFormula AP) : (♢ (♢ ϕ)) ≡ (♢ ϕ) := by
  simp [Equivalent.Equiv]
  funext σ
  simp [Worlds]
  rw [world_satisfies_eventually, world_satisfies_eventually]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h
    rw [world_satisfies_eventually] at hi
    obtain ⟨j, hj⟩ := hi
    use i + j
    rw [suffix_composition] at hj
    assumption
  · intro h
    obtain ⟨i, hi⟩ := h
    use 0
    rw [world_satisfies_eventually]
    use i
    rw [suffix_composition]
    ring_nf
    assumption

theorem ltl_idempotence_always {AP: Type} (ϕ : LTLFormula AP) : (□ (□ ϕ)) ≡ (□ ϕ) := by
  simp [Equivalent.Equiv]
  funext σ
  simp [Worlds]
  rw [world_satisfies_always, world_satisfies_always]
  constructor
  · intro h
    intro i
    specialize h i
    rw [world_satisfies_always] at h
    specialize h 0
    rw [suffix_composition] at h
    assumption
  · intro h
    intro i
    rw [world_satisfies_always]
    intro j
    rw [suffix_composition]
    specialize h (i + j)
    assumption

theorem ltl_idempotence_until_left {AP: Type} (ϕ ψ : LTLFormula AP) : ((ϕ 𝓤 ϕ) 𝓤 ψ) ≡ (ϕ 𝓤 ψ) := by
  simp [Equivalent.Equiv]
  funext σ
  simp [Worlds]
  simp [Satisfaction.Satisfies]
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
      rw [suffix_composition] at hkl
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
        rw [suffix_composition] at hkr
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
      rw [suffix_composition, Nat.add_zero]
      specialize hr k hk
      constructor
      · assumption
      · intro k'
        intro hk'
        simp at hk'

theorem ltl_idempotence_until_right {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ 𝓤 (ψ 𝓤 ψ)) ≡ (ϕ 𝓤 ψ) := by
  simp [Equivalent.Equiv]
  funext σ
  simp [Worlds]
  simp [Satisfaction.Satisfies]
  rw [world_satisfies_ltl, world_satisfies_ltl]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := h
    use j
    obtain ⟨hl, hr⟩ := hj
    rw [world_satisfies_ltl] at hl
    obtain ⟨j', hj'⟩ := hl
    obtain ⟨hjl, hjr⟩ := hj'
    rw [suffix_composition] at hjl
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
      rw [suffix_composition] at hjr
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
      rw [suffix_composition, Nat.add_zero]
      constructor
      · assumption
      · intro k
        intro hk
        simp at hk
    · assumption

theorem ltl_absorption_always_eventually {AP: Type} (ϕ : LTLFormula AP) : (♢ □ ♢ ϕ) ≡ (□ ♢ ϕ) := by
  simp [Equivalent.Equiv]
  funext σ
  simp [Worlds]
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
    rw [suffix_composition] at hj
    rw [← Nat.add_assoc, Nat.add_comm i' i]
    rw [← Nat.add_assoc] at hj
    assumption
  · intro h
    use 0
    rw [suffix_zero_identity]
    assumption

theorem ltl_absorption_eventually_always {AP: Type} (ϕ : LTLFormula AP) : (□ ♢ □ ϕ) ≡ (♢ □ ϕ) := by
  simp [Equivalent.Equiv]
  funext σ
  simp [Worlds]
  rw [world_satisfies_always]
  constructor
  · intro h
    specialize h 0
    rw [suffix_zero_identity] at h
    assumption
  · intro h
    intro i
    rw [world_satisfies_eventually_always] at h
    obtain ⟨i', hi⟩ := h
    rw [world_satisfies_eventually_always]
    use i'
    intro j
    specialize hi (i + j)
    rw [suffix_composition]
    rw [← Nat.add_assoc]
    rw [← Nat.add_assoc, Nat.add_comm i' i] at hi
    assumption

theorem ltl_expansion_until {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ 𝓤 ψ) ≡ (ψ ∨ (ϕ ∧ (◯ (ϕ 𝓤 ψ)))) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [world_satisfies_or]
  simp [Satisfaction.Satisfies]
  constructor
  · intro h
    rw [world_satisfies_ltl] at h
    obtain ⟨j, hj⟩ := h
    obtain ⟨hl, hr⟩ := hj
    rw [world_satisfies_ltl]
    cases c: j with
    | zero =>
      rw [c] at hl
      rw [suffix_zero_identity] at hl
      left
      assumption
    | succ n =>
      right
      have p : 0 < j := by
        rw [c]
        apply Nat.zero_lt_succ
      have hr' := hr 0 p
      rw [suffix_zero_identity] at hr'
      constructor
      · assumption
      · repeat rw [world_satisfies_ltl]
        use n
        rw [suffix_composition]
        rw [c] at hl
        rw [Nat.add_comm]
        constructor
        · assumption
        · intro k
          intro hk
          rw [suffix_composition]
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
        rw [suffix_zero_identity]
        constructor
        · assumption
        · simp
    | inr hr =>
        rw [world_satisfies_ltl] at hr
        obtain ⟨hll, hrr⟩ := hr
        repeat rw [world_satisfies_ltl] at hrr
        obtain ⟨j, hj⟩ := hrr
        use j + 1
        rw [suffix_composition, Nat.add_comm] at hj
        obtain ⟨hjl, hjr⟩ := hj
        constructor
        · assumption
        · intro k
          intro hk
          cases c: k with
          | zero =>
            rw [suffix_zero_identity]
            assumption
          | succ n =>
            rw [c] at hk
            rw [Nat.succ_lt_succ_iff] at hk
            specialize hjr n hk
            rw [suffix_composition] at hjr
            rw [Nat.add_comm]
            assumption

theorem ltl_expansion_eventually {AP: Type} (ϕ : LTLFormula AP) : (♢ ϕ) ≡ (ϕ ∨ (◯ (♢ ϕ))) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [world_satisfies_or]
  simp
  constructor
  · intro h
    rw [world_satisfies_eventually] at h
    obtain ⟨i, hi⟩ := h
    cases c: i with
    | zero =>
      rw [c] at hi
      rw [suffix_zero_identity] at hi
      left
      assumption
    | succ n =>
      right
      rw [world_satisfies_next]
      rw [world_satisfies_eventually]
      use n
      rw [suffix_composition]
      rw [c] at hi
      rw [Nat.add_comm]
      assumption
  · intro h
    rw [world_satisfies_eventually]
    cases h with
    | inl hl =>
      use 0
      rw [suffix_zero_identity]
      assumption
    | inr hr =>
      rw [world_satisfies_next] at hr
      rw [world_satisfies_eventually] at hr
      obtain ⟨j, hj⟩ := hr
      use j + 1
      rw [suffix_composition, Nat.add_comm] at hj
      assumption

theorem ltl_expansion_always {AP: Type} (ϕ : LTLFormula AP) : (□ ϕ) ≡ (ϕ ∧ (◯ (□ ϕ))) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [world_satisfies_and]
  simp
  rw [world_satisfies_next]
  repeat rw [world_satisfies_always]
  constructor
  · intro h
    constructor
    · specialize h 0
      rw [suffix_zero_identity] at h
      assumption
    · intro i
      specialize h (i + 1)
      rw [suffix_composition, Nat.add_comm]
      assumption
  · intro h
    intro i
    obtain ⟨hl, hr⟩ := h
    cases c: i with
    | zero =>
      rw [suffix_zero_identity]
      assumption
    | succ n =>
      specialize hr n
      rw [suffix_composition, Nat.add_comm] at hr
      assumption

theorem ltl_distributive_next_until {AP: Type} (ϕ ψ : LTLFormula AP) : (◯ (ϕ 𝓤 ψ)) ≡ ((◯ ϕ) 𝓤 (◯ ψ)) := by
  simp only [Equivalent.Equiv]
  funext σ
  simp only [Worlds]
  rw [world_satisfies_next]
  repeat rw [world_satisfies_until]
  simp
  constructor
  · intro h
    obtain ⟨j, hj⟩ := h
    use j
    rw [suffix_composition] at hj
    rw [world_satisfies_next]
    rw [suffix_composition]
    rw [Nat.add_comm]
    obtain ⟨hl, hr⟩ := hj
    constructor
    · assumption
    · intro k
      intro hk
      specialize hr k hk
      rw [world_satisfies_next]
      rw [suffix_composition]
      rw [suffix_composition] at hr
      rw [Nat.add_comm]
      assumption
  · intro h
    obtain ⟨j, hj⟩ := h
    use j
    rw [world_satisfies_next] at hj
    rw [suffix_composition] at hj
    rw [suffix_composition]
    rw [Nat.add_comm]
    obtain ⟨hl, hr⟩ := hj
    constructor
    · assumption
    · intro k
      intro hk
      specialize hr k hk
      rw [world_satisfies_next] at hr
      rw [suffix_composition]
      rw [suffix_composition] at hr
      rw [Nat.add_comm]
      assumption

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
Now we prove the lemma that "Until is the Least Solution of the Expansion Law"
-/
def solution_of_expansion_law {AP: Type} (ϕ ψ : LTLFormula AP) (P : Set (World AP)) : Prop := (Worlds ψ ∪ {σ ∈ Worlds ϕ | σ[1…] ∈ P}) ⊆ P

theorem until_least_solution_of_expansion_law {AP: Type} (ϕ ψ : LTLFormula AP) : (solution_of_expansion_law ϕ ψ (Worlds (ϕ 𝓤 ψ))) ∧ (∀ P, (solution_of_expansion_law ϕ ψ P) → Worlds (ϕ 𝓤 ψ) ⊆ P) := by
  unfold solution_of_expansion_law
  unfold Worlds
  simp
  constructor

  -- we first show that it is indeed a solution
  · constructor
    · intro σ
      intro h
      rw [Set.mem_def] at h
      rw [Set.mem_def]
      rw [world_satisfies_until]
      use 0
      rw [suffix_zero_identity]
      constructor
      · assumption
      · intro k
        intro hk
        simp at hk
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
      rw [suffix_composition] at hj
      use (1 + j)
      obtain ⟨hjl, hjr⟩ := hj
      constructor
      · assumption
      · intro k
        intro hk
        cases c: k with
        | zero =>
          rw [suffix_zero_identity]
          assumption
        | succ n =>
          rw [c] at hk
          rw [Nat.add_comm 1 j] at hk
          rw [Nat.succ_lt_succ_iff] at hk
          specialize hjr n hk
          rw [suffix_composition] at hjr
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
        simp at hn
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
        · rw [suffix_composition]
          assumption

    have h₀ : σ[0…] ∈ P := by
      apply b j 0
      simp

    rw [suffix_zero_identity] at h₀
    assumption

/-!
We will now use the satisfaction of LTL formulae to define satisfaction of PL formulae.
-/
instance {AP: Type} : Satisfaction (Set AP) (PLFormula AP) := ⟨fun A Φ ↦ A ⊨ Φ.formula⟩

/-!
We will also define some useful lemmas for satisfaction of PL formulae.
-/
def set_satisfies_negation {AP: Type} (σ : Set AP) (ϕ : PLFormula AP) : (σ ⊨ (¬ ϕ)) ↔ (¬ (σ ⊨ ϕ)) := by
  simp [Satisfaction.Satisfies]
  rw [world_satisfies_ltl]

def set_satisfies_or {AP: Type} (σ : Set AP) (ϕ₁ ϕ₂ : PLFormula AP) : (σ ⊨ (ϕ₁ ∨ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∨ (σ ⊨ ϕ₂)) := by
  simp [Satisfaction.Satisfies]
  repeat rw [world_satisfies_ltl]
  simp [Or.or, Not.not]
  constructor
  · intro h
    contrapose h
    simp at h
    simp
    assumption
  · intro h
    contrapose h
    simp at h
    simp
    assumption

def set_satisfies_and {AP: Type} (σ : Set AP) (ϕ₁ ϕ₂ : PLFormula AP) : (σ ⊨ (ϕ₁ ∧ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∧ (σ ⊨ ϕ₂)) := by
  simp [Satisfaction.Satisfies]
  repeat rw [world_satisfies_ltl]

end section

section
open TransitionSystem
/-!
We will define a satisfaction relation between transition systems and LT properties. For this, both must be defined over the same set of atomic propositions. Note that we specifically deal with Transition Systems without terminal states.
-/
instance {AP: Type} : Satisfaction (TransitionSystemWTS AP) (LTProperty AP) := ⟨fun TSwts P ↦ TracesWTS TSwts ⊆ P⟩

instance {AP: Type} {TSwts: TransitionSystemWTS AP} : Satisfaction (TSwts.TS.S) (LTProperty AP) := ⟨fun s P ↦ TracesFromStateWTS s ⊆ P⟩

-- We need to define membership of an Infinite Trace in an LT Property
instance {AP: Type} : Membership (InfiniteTrace AP) (LTProperty AP) := ⟨fun P π ↦ by
  rw [LTProperty] at P
  rw [InfiniteTrace] at π
  exact π ∈ P⟩

/-!
Some auxiliary lemmas about satisfaction of LT properties.
-/
theorem ltproperty_satisfaction_allPaths {AP: Type} (TSwts: TransitionSystemWTS AP) (P: LTProperty AP) : TSwts ⊨ P ↔ ∀ π, (h: π ∈ Paths TSwts.TS) → TraceFromPathWTS π h ∈ P := by
  simp [Satisfaction.Satisfies]
  rw [TracesWTS]
  simp
  constructor
  · intro h
    intro π
    intro h'
    rw [Paths] at h'
    simp at h'
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
    simp
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
      simp at hπ'
      simp
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
We now prove a theorem about **Trace Inclusion and LT Properties**.
-/
theorem trace_inclusion_and_LTProperties {AP: Type} (TSwts₁ TSwts₂: TransitionSystemWTS AP) : (TracesWTS TSwts₁ ⊆ TracesWTS TSwts₂) ↔ ∀ (P: LTProperty AP), TSwts₂ ⊨ P → TSwts₁ ⊨ P := by
  simp [Satisfaction.Satisfies]
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
    simp at h
    assumption


/-!
We will define the notion of trace equivalence between two transition systems, and then show a corollary of the previous theorem about **Trace Equivalence and LT Properties**.
-/
def trace_equivalence {AP: Type} (TS₁ TS₂: TransitionSystem AP) : Prop := Traces TS₁ = Traces TS₂

def trace_equivalence_wts {AP: Type} (TSwts₁ TSwts₂: TransitionSystemWTS AP) : Prop := TracesWTS TSwts₁ = TracesWTS TSwts₂

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
We will now define some special kinds of LT properties, starting with **Invariants**.
-/
def isInvariantWithFormula {AP: Type} (P: LTProperty AP) (ϕ: PLFormula AP) : Prop := P = {σ | ∀ (n: ℕ), σ n ⊨ ϕ}
def isInvariant {AP: Type} (P: LTProperty AP) : Prop := ∃ (ϕ : PLFormula AP), isInvariantWithFormula P ϕ


theorem invariant_satisfaction_reachability {AP: Type} (TSwts: TransitionSystemWTS AP) (P: LTProperty AP) (h: isInvariant P) : TSwts ⊨ P ↔ (∃ (ϕ : PLFormula AP), (isInvariantWithFormula P ϕ) ∧ (∀ s ∈ Reach TSwts.TS, TSwts.TS.L s ⊨ ϕ)) := by
  rw [ltproperty_satisfaction_allPaths]
  rw [isInvariant] at h
  obtain ⟨ϕ, hϕ⟩ := h
  unfold isInvariantWithFormula at hϕ
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
      simp at hs
      unfold isReachableState at hs
      obtain ⟨n, e, he⟩ := hs
      obtain ⟨hel, her⟩ := he
      let πtail : FinitePathFragment TS n := finiteExecutionFragmentToFinitePathFragment e
      have htail : πtail.states = e.states := by
        unfold πtail finiteExecutionFragmentToFinitePathFragment
        simp
      obtain ⟨tailStates, tailValid⟩ := πtail
      simp at htail
      have hhead : ∃ π', π' ∈ PathsFromState s := path_originates_from_state_if_noTerminalState hTS s
      obtain ⟨πhead, hπhead⟩ := hhead
      simp
      simp at πhead
      simp at h'
      simp at s
      cases c: πhead with
      | @finite n p =>
        rw [c] at hπhead
        unfold PathsFromState at hπhead
        simp at hπhead
        obtain ⟨hπheadmax, _⟩ := hπhead
        unfold isMaximalPathFragment endStatePathFragment at hπheadmax
        simp at hπheadmax
        specialize hTS (p.states (Fin.last n))
        contradiction
      | infinite p =>
        rw [c] at hπhead
        obtain ⟨headStates, headValid⟩ := p

        unfold PathsFromState startStatePathFragment at hπhead
        simp at hπhead
        obtain ⟨_, headState0⟩ := hπhead

        -- combine πtail and πhead to form a path
        let π := PathFragment.infinite (⟨fun i => if i < n then tailStates i else headStates (i - n),
          by
            intro i
            simp
            if h : i < n then
              let v := tailValid (Fin.mk i h)
              simp at v
              simp [h]
              if h': i + 1 < n then
                simp [h']
                exact v
              else
                simp at h'
                rw [Nat.lt_iff_add_one_le] at h
                have p : i + 1 = n := by apply Nat.le_antisymm <;> assumption
                rw [p]
                simp
                rw [headState0]
                if hn: n = 0 then
                  rw [hn] at p
                  simp at p
                else
                  have hnsucc : ∃ m, n = m + 1 := by
                    apply Nat.exists_eq_succ_of_ne_zero
                    assumption
                  obtain ⟨m, hm⟩ := hnsucc
                  rw [hm] at p
                  simp at p
                  rw [p]
                  let v := tailValid (Fin.mk m (by rw [hm]; simp))
                  simp at v
                  have hv : tailStates (m + 1) = s := by
                    rw [htail]
                    unfold endStateExecutionFragment at her
                    rw [← Fin.natCast_eq_last] at her
                    rw [← her]
                    simp [hm]
                  rw [← hv]
                  exact v
            else
              simp [h]
              simp at h
              have h' : ¬ (i + 1 < n) := by
                simp only [LTLFormula.Not.not]
                contrapose h
                simp at h
                rw [Nat.not_le]
                have hii : i < i + 1 := by simp
                apply Nat.lt_trans hii h
              simp only [LTLFormula.Not.not] at h'
              simp [h']
              let v : headStates (i - n + 1) ∈ Post (headStates (i - n)) := headValid (i - n)
              rw [Nat.sub_add_comm h]
              exact v
            ⟩: InfinitePathFragment TS)

        have hπ : π ∈ Paths TS := by
          unfold Paths isPath isInitialPathFragment isMaximalPathFragment endStatePathFragment
          simp
          constructor
          · unfold startStatePathFragment π
            simp
            unfold isInitialExecutionFragment startStateExecutionFragment at hel
            simp at hel
            cases n with
            | zero =>
              simp
              rw [headState0]
              unfold endStateExecutionFragment at her
              rw [← Fin.natCast_eq_last] at her
              rw [← her]
              simp [hel]
            | succ m =>
              simp
              rw [htail]
              assumption
          · unfold π
            simp

        specialize h' π hπ
        rw [hϕ] at h'
        rw [Set.mem_def] at h'
        rw [Set.setOf_app_iff] at h'
        specialize h' n

        have hs : (@TraceFromPathWTS AP ⟨TS, hTS⟩ π hπ) n = TS.L s := by
          unfold π TraceFromPathWTS InfiniteTraceFromInfinitePathFragment
          simp only [TraceFromPathWTS.proof_2]
          sorry

        rw [hs] at h'
        assumption
  · intro h
    intro π
    intro hπ
    simp at hπ
    rw [hϕ, Set.mem_def]
    rw [Set.setOf_app_iff]
    intro n
    obtain ⟨Φ, hΦ⟩ := h
    obtain ⟨hΦl, hΦr⟩ := hΦ
    sorry

end section
