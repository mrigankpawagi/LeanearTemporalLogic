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

structure FiniteWorld (AP: Type) where
  n : ℕ
  f : Fin (n + 1) → Set AP

/-!
A suffix of a world w starting at index i is a world w' such that w'(j) = w(i+j) for all j. We will denote this by w[i...].
-/
def Suffix {AP: Type} (σ : World AP) (i : ℕ) : World AP := fun j => σ (i + j)

syntax:60 term "[" term "…]" : term
macro_rules
  | `($σ[$i…]) => `(Suffix $σ $i)

/-!
A simple lemma for composition of suffixes.
-/
theorem Suffix.composition {AP: Type} (σ : World AP) (i j : ℕ) : σ[i…][j…] = σ[i+j…] := by
  funext k
  unfold Suffix
  rw [Nat.add_assoc]

theorem Suffix.zero_identity {AP: Type} (σ : World AP) : σ[0…] = σ := by
  funext k
  unfold Suffix
  rw [Nat.zero_add]

/-!
We will also need prefixes of worlds. Note that prefixes are finite.
-/
def Prefix {AP: Type} (σ : World AP) (n: ℕ) : FiniteWorld AP := ⟨n, fun i => σ i⟩

def PrefixOfPrefix {AP: Type} (ω : FiniteWorld AP) (m : ℕ) (h: m ≤ ω.n) : FiniteWorld AP := ⟨m, fun i => ω.f (Fin.castLE (by simp[h]) i)⟩

def pref {AP: Type} (σ: World AP) : Set (FiniteWorld AP) := fun ω => ∃ (n: ℕ), ω = Prefix σ n

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
    rw [Suffix.composition] at h
    assumption
  · intro h
    intro i
    rw [world_satisfies_always]
    intro j
    rw [Suffix.composition]
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
    rw [Suffix.composition] at hj
    rw [← Nat.add_assoc, Nat.add_comm i' i]
    rw [← Nat.add_assoc] at hj
    assumption
  · intro h
    use 0
    rw [Suffix.zero_identity]
    assumption

theorem ltl_absorption_eventually_always {AP: Type} (ϕ : LTLFormula AP) : (□ ♢ □ ϕ) ≡ (♢ □ ϕ) := by
  simp [Equivalent.Equiv]
  funext σ
  simp [Worlds]
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
        · simp
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
      rw [Suffix.zero_identity]
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
        · rw [Suffix.composition]
          assumption

    have h₀ : σ[0…] ∈ P := by
      apply b j 0
      simp

    rw [Suffix.zero_identity] at h₀
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

/-!
We define some coercions and membership relations to easily work with traces and LT properties.
-/
instance {AP: Type} : Coe (FiniteWorld AP) (FiniteTrace AP) := ⟨fun ω => ⟨ω.n, ω.f⟩⟩
instance {AP: Type} : Coe (FiniteTrace AP) (FiniteWorld AP) := ⟨fun σ => ⟨σ.n, σ.f⟩⟩

instance {AP: Type} : Coe (Set (FiniteWorld AP)) (Set (FiniteTrace AP)) := ⟨fun S => {σ | ↑σ ∈ S}⟩
instance {AP: Type} : Coe (Set (FiniteTrace AP)) (Set (FiniteWorld AP)) := ⟨fun S => {ω | ↑ω ∈ S}⟩

instance {AP: Type} : Membership (InfiniteTrace AP) (LTProperty AP) := ⟨fun P π ↦ by
  rw [LTProperty] at P
  rw [InfiniteTrace] at π
  exact π ∈ P⟩

instance {AP: Type} : Satisfaction (TransitionSystemWTS AP) (Set (World AP)) := ⟨fun TSwts P ↦ TracesWTS TSwts ⊆ P⟩

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
def isInvariantWithCondition {AP: Type} (P: LTProperty AP) (ϕ: PLFormula AP) : Prop := P = {σ | ∀ (n: ℕ), σ n ⊨ ϕ}
def isInvariant {AP: Type} (P: LTProperty AP) : Prop := ∃ (ϕ : PLFormula AP), isInvariantWithCondition P ϕ

theorem invariant_satisfaction_reachability {AP: Type} (TSwts: TransitionSystemWTS AP) (P: LTProperty AP) (h: isInvariant P) : TSwts ⊨ P ↔ (∃ (ϕ : PLFormula AP), (isInvariantWithCondition P ϕ) ∧ (∀ s ∈ Reach TSwts.TS, TSwts.TS.L s ⊨ ϕ)) := by
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
      simp at hs
      unfold isReachableState at hs
      obtain ⟨e, he⟩ := hs
      obtain ⟨hel, her⟩ := he
      let πtail : FinitePathFragment TS := finiteExecutionFragmentToFinitePathFragment e
      have htail : πtail.states = e.states := by
        unfold πtail finiteExecutionFragmentToFinitePathFragment
        simp
      have en : e.n = πtail.n := by
        unfold πtail finiteExecutionFragmentToFinitePathFragment
        simp
      simp at en
      simp at htail
      have hhead : ∃ π', π' ∈ PathsFromState s := path_originates_from_state_if_noTerminalState hTS s
      obtain ⟨πhead, hπhead⟩ := hhead
      simp
      simp at πhead
      simp at h'
      simp at s
      cases c: πhead with
      | finite p =>
        rw [c] at hπhead
        unfold PathsFromState at hπhead
        simp at hπhead
        obtain ⟨hπheadmax, _⟩ := hπhead
        unfold isMaximalPathFragment endStatePathFragment at hπheadmax
        simp at hπheadmax
        specialize hTS (p.states (Fin.last p.n))
        contradiction
      | infinite p =>
        rw [c] at hπhead
        obtain ⟨headStates, headValid⟩ := p

        unfold PathsFromState startStatePathFragment at hπhead
        simp at hπhead
        obtain ⟨_, headState0⟩ := hπhead

        -- combine πtail and πhead to form a path
        let π := PathFragment.infinite (PathFragment.concatenate_finite_and_infinite πtail ⟨headStates, headValid⟩ (by
          rw [htail]
          unfold endStateExecutionFragment at her
          simp
          rw [headState0]
          have heq : Fin.last e.n = Fin.last πtail.n := by
            rw [← Fin.natCast_eq_last]
            rw [← Fin.natCast_eq_last]
            simp [en]
          rw [← heq]
          assumption
          ))

        have hπ : π ∈ Paths TS := by
          unfold Paths isPath isInitialPathFragment isMaximalPathFragment endStatePathFragment
          simp
          constructor
          · unfold startStatePathFragment π
            simp
            unfold isInitialExecutionFragment startStateExecutionFragment at hel
            simp at hel
            unfold PathFragment.concatenate_finite_and_infinite
            simp
            cases cc: e.n with
            | zero =>
              rw [headState0]
              simp [← en, cc]
              unfold endStateExecutionFragment at her
              rw [← Fin.natCast_eq_last] at her
              simp [cc] at her
              rw [← her]
              simp [hel]
            | succ m =>
              rw [htail]
              simp [← en, cc]
              apply hel
          · unfold π
            simp

        specialize h' π hπ
        rw [hϕ] at h'
        rw [Set.mem_def] at h'
        rw [Set.setOf_app_iff] at h'
        specialize h' e.n

        have hs : (@TraceFromPathWTS AP ⟨TS, hTS⟩ π hπ) e.n = TS.L s := by
          unfold TraceFromPathWTS InfiniteTraceFromInfinitePathFragment
          unfold Paths isPath at hπ
          simp at hπ
          obtain ⟨hπl, hπr⟩ := hπ
          rw [maximalIffInfinitePathFragment hTS'] at hπr
          simp
          match c: π with
          | PathFragment.finite p =>
            simp
            contradiction
          | PathFragment.infinite p =>
            simp
            unfold endStateExecutionFragment at her
            unfold π at c
            simp at c
            rw [← c]
            unfold PathFragment.concatenate_finite_and_infinite
            simp [en]
            rw [headState0]

        rw [hs] at h'
        assumption
  · intro h'
    intro π
    intro hπ
    simp at π
    simp at hπ
    obtain ⟨Φ, hΦ⟩ := h'
    obtain ⟨hΦl, hΦr⟩ := hΦ
    unfold isInvariantWithCondition at hΦl
    simp at hΦr
    rw [hΦl, Set.mem_def, Set.setOf_app_iff]
    intro n
    unfold TraceFromPathWTS InfiniteTraceFromInfinitePathFragment
    cases π with
    | finite _ =>
      unfold Paths isPath at hπ
      simp at hπ
      obtain ⟨hπl, hπr⟩ := hπ
      simp
      contradiction
    | infinite p =>
      simp
      have hreach : p.states n ∈ Reach TS := by
        unfold Reach isReachableState
        simp
        let eInf := infinitePathFragmentToInfiniteExecutionFragment p
        let e : FiniteExecutionFragment TS := ⟨n, fun i => eInf.states i, fun i => eInf.actions i, by
          intro i
          simp
          exact eInf.valid i⟩
        use e
        constructor
        · unfold isInitialExecutionFragment startStateExecutionFragment
          simp
          unfold Paths isPath at hπ
          simp at hπ
          obtain ⟨hπl, hπr⟩ := hπ
          unfold isInitialPathFragment startStatePathFragment at hπl
          simp at hπl
          unfold e eInf infinitePathFragmentToInfiniteExecutionFragment
          simp
          assumption
        · unfold endStateExecutionFragment e eInf infinitePathFragmentToInfiniteExecutionFragment
          simp
      specialize hΦr (p.states n) hreach
      assumption


def isSafetyProperty {AP: Type} (P: LTProperty AP) : Prop := ∀ (σ: World AP), σ ∉ P → ∃ n, ∀ σ', (Prefix σ' n = Prefix σ n) → σ' ∉ P

def isBadPrefix {AP: Type} (P: LTProperty AP) (ω: FiniteWorld AP) : Prop := isSafetyProperty P ∧ ∀ σ, (Prefix σ (ω.n) = ω) → σ ∉ P

def isMinimalBadPrefix {AP: Type} (P: LTProperty AP) (ω: FiniteWorld AP) : Prop := isBadPrefix P ω ∧ ∀ (m: ℕ) (h: m < ω.n), ¬ (isBadPrefix P (PrefixOfPrefix ω m (by
  rw [Nat.le_iff_lt_or_eq]
  left
  assumption
)))

/-! Set of all bad prefixes -/
def BadPref {AP: Type} (P: LTProperty AP) : Set (FiniteWorld AP) := { ω | isBadPrefix P ω}

/-! Set of all minimal bad prefixes -/
def MinBadPref {AP: Type} (P: LTProperty AP) : Set (FiniteWorld AP) := { ω | isMinimalBadPrefix P ω}

theorem safety_satisfaction {AP: Type} (TSwts: TransitionSystemWTS AP) (P: LTProperty AP) (h: isSafetyProperty P) : TSwts ⊨ P ↔ ∀ ω ∈ BadPref P, ↑ω ∉ TracesFin TSwts.TS := by
  have hTS := TSwts.h
  unfold hasNoTerminalStates at hTS
  constructor
  · intro h₁
    by_contra h₂
    simp at h₂
    obtain ⟨ω, hω⟩ := h₂
    obtain ⟨hω₁, hω₂⟩ := hω
    simp [Satisfaction.Satisfies] at h₁
    unfold TracesWTS at h₁
    simp at h₁
    unfold BadPref isBadPrefix at hω₁
    simp at hω₁
    obtain ⟨_, hω₁⟩ := hω₁
    simp [Membership.mem] at hω₂
    obtain ⟨s, hs⟩ := hω₂
    obtain ⟨hsi, hp⟩ := hs
    rw [Set.mem_def, Set.setOf_app_iff] at hsi
    unfold TracesFinFromState at hp
    simp at hp
    obtain ⟨π, hπ⟩ := hp
    obtain ⟨hπl, hπr⟩ := hπ
    let hinfπ := path_originates_from_state_if_noTerminalState hTS (π.states (Fin.last π.n))
    obtain ⟨πinf, hπinf⟩ := hinfπ

    match πinf with
    | PathFragment.finite p =>
      unfold PathsFromState at hπinf
      simp at hπinf
      obtain ⟨hmax, _⟩ := hπinf
      unfold isMaximalPathFragment endStatePathFragment at hmax
      simp at hmax
      specialize hTS (p.states (Fin.last p.n))
      contradiction
    | PathFragment.infinite p =>
      have hcont : π.states (Fin.last π.n) = p.states 0 := by
        unfold PathsFromState at hπinf
        simp at hπinf
        obtain ⟨_, hstart⟩ := hπinf
        unfold startStatePathFragment at hstart
        simp at hstart
        rw [hstart]
      let π' := PathFragment.concatenate_finite_and_infinite π p hcont

      let Trace := InfiniteTraceFromInfinitePathFragment π'
      let σ : World AP := Trace
      have hpref : Prefix σ ω.n = ω := by
        unfold Prefix
        obtain ⟨n, f⟩ := ω
        simp
        funext i
        simp at hπr
        unfold σ Trace InfiniteTraceFromInfinitePathFragment π' PathFragment.concatenate_finite_and_infinite
        simp
        unfold FiniteTraceFromFinitePathFragment at hπr
        simp at hπr
        obtain ⟨heq, hfeq⟩ := hπr
        rw [propext (Fin.heq_fun_iff (congrFun (congrArg HAdd.hAdd heq) 1))] at hfeq
        if c: i < n then
          have h': (i: ℕ) < π.n := by
            rw [heq]
            rw [@Fin.lt_iff_val_lt_val] at c
            simp at c
            simp [c]
          have h'' : (i: ℕ) < π.n + 1 := by
            apply Nat.lt_add_one_of_lt
            assumption
          simp [h']
          rw [hfeq]
          simp [Nat.mod_eq_of_lt h'']
        else
          simp at c
          rw [c]
          simp
          simp [heq]
          specialize hfeq i
          simp [c] at hfeq
          rw [← hcont, ← Fin.natCast_eq_last]
          simp [heq]
          rw [hfeq]
          simp [heq]
          unfold Fin.last
          simp
      specialize hω₁ σ hpref
      specialize h₁ s hsi
      unfold TracesFromInitialStateWTS at h₁
      rw [Set.setOf_subset] at h₁
      simp at h₁

      specialize h₁ Trace (PathFragment.infinite π')
      have hpath : (PathFragment.infinite π') ∈ PathsFromState s := by
        unfold π' PathFragment.concatenate_finite_and_infinite PathsFromState isMaximalPathFragment endStatePathFragment startStatePathFragment
        simp
        if c: 0 < π.n then
          simp [c]
          unfold PathsFinFromState startStatePathFragment at hπl
          simp at hπl
          assumption
        else
          simp [c]
          simp at c
          unfold PathsFinFromState startStatePathFragment at hπl
          simp at hπl
          rw [← hcont, ← hπl]
          rw [← Fin.natCast_eq_last]
          simp [c]

      specialize h₁ hpath
      have htr : Trace = TraceFromPathFromInitialStateWTS s (PathFragment.infinite π') hpath hsi := by
        unfold Trace TraceFromPathFromInitialStateWTS TraceFromPathWTS
        simp

      rw [htr] at h₁
      simp at h₁
      rw [← htr] at h₁
      unfold σ at hω₁
      contradiction
  · intro h₁
    by_contra h₂
    simp [Satisfaction.Satisfies] at h₂
    unfold TracesWTS TracesFromInitialStateWTS at h₂
    simp at h₂
    obtain ⟨s, hs, h₂⟩ := h₂
    rw [Set.subset_def] at h₂
    simp at h₂
    obtain ⟨trace, hπ, h₂⟩ := h₂
    obtain ⟨π, hπpath, hπ⟩ := hπ

    let hsafe := h
    unfold isSafetyProperty at h
    specialize h trace
    apply h at h₂
    obtain ⟨nω, hbad⟩ := h₂
    let ω : FiniteWorld AP := ⟨nω, fun i => trace i⟩
    specialize h₁ ω
    unfold BadPref isBadPrefix at h₁
    simp [hsafe] at h₁
    have h' : True ∧ ∀ (σ : World AP), Prefix σ ω.n = ω → σ ∉ P := by constructor <;> trivial
    apply h₁ at h'
    unfold TracesFin TracesFinFromState at h'
    simp at h'
    simp [Membership.mem] at h'
    simp [Set.Mem] at h'
    specialize h' s hs

    match π with
    | PathFragment.finite p =>
      unfold PathsFromState isMaximalPathFragment endStatePathFragment at hπpath
      simp at hπpath
      obtain ⟨hπl, hπr⟩ := hπpath
      specialize hTS (p.states (Fin.last p.n))
      contradiction
    | PathFragment.infinite p =>
      let πfin : FinitePathFragment TSwts.TS := ⟨nω, fun i => p.states i, by
      intro i
      have hv := p.valid i
      simp
      exact hv⟩
      specialize h' πfin

      have h₀ : PathsFinFromState s πfin := by
        unfold PathsFinFromState startStatePathFragment πfin
        rw [Set.setOf_app_iff]
        simp
        unfold PathsFromState isMaximalPathFragment endStatePathFragment startStatePathFragment at hπpath
        simp at hπpath
        assumption

      have h₀' : FiniteTraceFromFinitePathFragment πfin = { n := nω, f := ω.f } := by
        unfold FiniteTraceFromFinitePathFragment πfin ω
        simp
        funext i
        rw [hπ]
        unfold TraceFromPathFromInitialStateWTS TraceFromPathWTS InfiniteTraceFromInfinitePathFragment
        simp

      apply h' at h₀
      apply h₀ at h₀'
      apply h₀'

/-!
We will define prefixes and closures for LT properties to provide an alternative characterization of safety properties.
-/
def prefLTProperty {AP: Type} (P: LTProperty AP) : Set (FiniteWorld AP) := ⋃ σ ∈ P, pref σ

def closureLTProperty {AP: Type} (P: LTProperty AP) : Set (World AP) := {σ | pref σ ⊆ prefLTProperty P}

instance {AP: Type} : HasSubset (LTProperty AP) := ⟨fun P Q ↦ ∀ σ, σ ∈ P → σ ∈ Q⟩

theorem closure_contains_property {AP: Type} (P: LTProperty AP) : P ⊆ (closureLTProperty P) := by
  rw [Set.subset_def]
  intro σ hσ
  unfold closureLTProperty prefLTProperty
  rw [Set.mem_def, Set.setOf_app_iff]
  rw [Set.subset_def]
  intro ω hω
  rw [Set.mem_iUnion]
  use σ
  simp
  exact ⟨hσ, hω⟩

theorem safety_closure {AP: Type} (P: LTProperty AP) : isSafetyProperty P ↔ closureLTProperty P = P := by
  constructor
  · intro h₁
    rw [Set.Subset.antisymm_iff]
    constructor
    · rw [Set.subset_def]
      by_contra hc
      simp at hc
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
      simp at hclos
      obtain ⟨σ', hσ'⟩ := hclos
      specialize h₁ σ'
      obtain ⟨hl, hr⟩ := hσ'
      unfold pref at hr
      rw [Set.mem_def] at hr
      obtain ⟨m, hr⟩ := hr
      have hnm : n = m := by
        unfold Prefix at hr
        simp at hr
        obtain ⟨h', _⟩ := hr
        assumption
      rw [← hnm] at hr
      rw [Eq.symm hr] at h₁
      simp [hr] at h₁
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
    simp at hp
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
    simp at hp
    specialize hp n
    rw [← hσ'] at hp
    contradiction

theorem closure_of_traces {AP: Type} (TSwts: TransitionSystemWTS AP) : isSafetyProperty (closureLTProperty (TracesWTS TSwts)) ∧ (TSwts ⊨ closureLTProperty (TracesWTS TSwts)) := by
  constructor
  · unfold isSafetyProperty
    intro σ hσ
    unfold closureLTProperty at hσ
    rw [Set.mem_def, Set.setOf_app_iff] at hσ
    unfold prefLTProperty at hσ
    rw [Set.subset_def] at hσ
    simp at hσ
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
    simp
    use ω
    constructor
    · unfold pref
      rw [Set.mem_def]
      use n
      rw [hσ']
    · assumption
  · simp [Satisfaction.Satisfies]
    unfold closureLTProperty
    rw [Set.subset_def]
    intro σ hσ
    rw [Set.mem_def, Set.setOf_app_iff]
    unfold prefLTProperty
    rw [Set.subset_def]
    intro ω hω
    rw [Set.mem_iUnion]
    use σ
    simp
    exact ⟨hσ, hω⟩

theorem finite_traces_are_prefixes {AP: Type} (TSwts: TransitionSystemWTS AP) : TracesFin TSwts.TS = prefLTProperty (TracesWTS TSwts) := by
  unfold prefLTProperty
  simp
  rw [Set.Subset.antisymm_iff, Set.subset_def, Set.subset_def]
  constructor
  · intro t ht
    unfold TracesFin at ht
    rw [Set.mem_def, Set.setOf_app_iff] at ht
    obtain ⟨s, hs, ht⟩ := ht
    simp at hs
    unfold TracesFinFromState at ht
    simp at ht
    obtain ⟨πtail, hπ⟩ := ht
    obtain ⟨hπl, hπr⟩ := hπ
    simp

    -- create a full path
    let hπhead := path_originates_from_state_if_noTerminalState TSwts.h (πtail.states (Fin.last πtail.n))
    obtain ⟨πhead, hπhead⟩ := hπhead
    match πhead with
    | PathFragment.finite p =>
      unfold PathsFromState at hπhead
      simp at hπhead
      obtain ⟨hπheadmax, _⟩ := hπhead
      unfold isMaximalPathFragment endStatePathFragment at hπheadmax
      simp at hπheadmax
      obtain ⟨_, hTS⟩ := TSwts
      specialize hTS (p.states (Fin.last p.n))
      contradiction
    | PathFragment.infinite p =>
      let π := PathFragment.concatenate_finite_and_infinite πtail p (by
        unfold PathsFromState startStatePathFragment at hπhead
        simp at hπhead
        obtain ⟨hπheadl, hπheadr⟩ := hπhead
        rw [hπheadr]
      )
      have htrace : PathFragment.infinite π ∈ TSwts.TS.Paths := by
        unfold Paths isPath isInitialPathFragment isMaximalPathFragment endStatePathFragment startStatePathFragment
        simp
        unfold π PathFragment.concatenate_finite_and_infinite
        simp
        if c: 0 < πtail.n then
          simp [c]
          unfold PathsFinFromState startStatePathFragment at hπl
          simp at hπl
          rw [hπl]
          assumption
        else
          simp [c]
          simp at c
          unfold PathsFinFromState startStatePathFragment at hπl
          simp at hπl
          unfold PathsFromState startStatePathFragment at hπhead
          simp at hπhead
          obtain ⟨_, hπhead⟩ := hπhead
          rw [hπhead]
          rw [← Fin.natCast_eq_last]
          simp [c]
          rw [hπl]
          assumption
      let trace := TraceFromPathWTS (PathFragment.infinite π) htrace
      use trace
      constructor
      · unfold trace TracesWTS TracesFromInitialStateWTS TraceFromPathWTS
        rw [Set.mem_iUnion]
        simp
        use s, hs
        use (PathFragment.infinite π)
        use (by
          unfold PathsFromState isMaximalPathFragment endStatePathFragment startStatePathFragment π
          unfold PathFragment.concatenate_finite_and_infinite
          simp
          if c: 0 < πtail.n then
            simp [c]
            unfold PathsFinFromState startStatePathFragment at hπl
            simp at hπl
            rw [hπl]
          else
            simp [c]
            simp at c
            unfold PathsFinFromState startStatePathFragment at hπl
            simp at hπl
            unfold PathsFromState startStatePathFragment at hπhead
            simp at hπhead
            obtain ⟨_, hπhead⟩ := hπhead
            rw [hπhead]
            rw [← Fin.natCast_eq_last]
            simp [c]
            rw [hπl])
        unfold TraceFromPathFromInitialStateWTS TraceFromPathWTS
        simp
      · unfold pref
        rw [Set.mem_def]
        use t.n
        rw [← hπr]
        unfold FiniteTraceFromFinitePathFragment
        unfold Prefix
        simp
        funext i
        unfold trace π PathFragment.concatenate_finite_and_infinite TraceFromPathWTS InfiniteTraceFromInfinitePathFragment
        simp
        if c: ↑i < πtail.n then
          simp [c]
        else
          obtain ⟨i, hi⟩ := i
          simp [c]
          simp at c
          have h': i ≤ πtail.n := by
            rw [Nat.le_iff_lt_add_one]
            assumption
          have heq : i = πtail.n := by apply Nat.le_antisymm <;> assumption
          simp [heq]
          unfold PathsFromState startStatePathFragment at hπhead
          simp at hπhead
          obtain ⟨_, hπhead⟩ := hπhead
          rw [hπhead]
          aesop

  · intro t ht
    unfold TracesFin TracesFinFromState
    simp
    rw [Set.mem_def, Set.setOf_app_iff] at ht
    obtain ⟨T, hT⟩ := ht
    obtain ⟨hT₁, hT₂⟩ := hT
    unfold TracesWTS TracesFromInitialStateWTS at hT₁
    rw [Set.mem_iUnion] at hT₁
    simp at hT₁
    obtain ⟨s, hs, hT₁⟩ := hT₁
    use s, hs
    obtain ⟨π, hπ, hT₁⟩ := hT₁
    unfold pref Prefix at hT₂
    rw [Set.mem_def] at hT₂
    simp at hT₂
    unfold TraceFromPathFromInitialStateWTS TraceFromPathWTS at hT₁
    cases π with
    | finite p =>
      unfold PathsFromState isMaximalPathFragment endStatePathFragment at hπ
      simp at hπ
      obtain ⟨hπ, _⟩ := hπ
      obtain ⟨_, hTS⟩ := TSwts
      specialize hTS (p.states (Fin.last p.n))
      contradiction
    | infinite p =>
      unfold InfiniteTraceFromInfinitePathFragment at hT₁
      simp at hT₁
      rw [hT₁] at hT₂
      simp at hT₂
      let πfin : FinitePathFragment TSwts.TS := ⟨t.n, fun i => p.states i, by
        intro i
        have hv := p.valid i
        simp
        exact hv⟩
      use πfin
      unfold PathsFinFromState startStatePathFragment
      simp
      constructor
      · unfold πfin
        simp
        unfold PathsFromState isMaximalPathFragment endStatePathFragment startStatePathFragment at hπ
        simp at hπ
        assumption
      · unfold FiniteTraceFromFinitePathFragment πfin
        simp
        obtain ⟨n, f⟩ := t
        simp
        simp at hT₂
        rw [hT₂]

theorem prefix_of_closure_is_prefix {AP: Type} (P : LTProperty AP) : prefLTProperty (closureLTProperty P) = prefLTProperty P := by
  rw [Set.Subset.antisymm_iff]
  constructor
  · unfold prefLTProperty
    rw [Set.subset_def]
    intro ω hω
    rw [Set.mem_iUnion] at hω
    obtain ⟨σ, hσ, hω⟩ := hω
    simp at hω
    rw [Set.mem_iUnion]
    simp
    obtain ⟨hω₁, hω₂⟩ := hω
    obtain ⟨hω₁, hω₃⟩ := hω₁
    rw [← hω₃] at hω₂
    unfold closureLTProperty at hω₁
    rw [Set.mem_def, Set.setOf_app_iff] at hω₁
    unfold prefLTProperty at hω₁
    rw [Set.subset_def] at hω₁
    specialize hω₁ ω hω₂
    rw [Set.mem_iUnion] at hω₁
    simp at hω₁
    obtain ⟨σ', hσ', hω₁⟩ := hω₁
    use σ'
  · unfold prefLTProperty
    rw [Set.subset_def]
    intro ω hω
    rw [Set.mem_iUnion] at hω
    obtain ⟨σ, hσ, hω⟩ := hω
    simp at hω
    rw [Set.mem_iUnion]
    simp
    obtain ⟨hω₁, hω₂⟩ := hω
    obtain ⟨hω₁, hω₃⟩ := hω₁
    rw [← hω₃] at hω₂
    unfold closureLTProperty
    use σ
    rw [Set.mem_def, Set.setOf_app_iff]
    unfold prefLTProperty
    rw [Set.subset_def]
    simp
    constructor
    · intro ω' hω'
      use σ
    · assumption

theorem prefix_monotonicity {AP: Type} {P₁ P₂ : LTProperty AP} : P₁ ⊆ P₂ → prefLTProperty P₁ ⊆ prefLTProperty P₂ := by
  repeat rw [Set.subset_def]
  intro h
  intro ω hω
  unfold prefLTProperty at hω
  rw [Set.mem_iUnion] at hω
  simp at hω
  obtain ⟨σ, hσ, hω⟩ := hω
  specialize h σ hσ
  unfold prefLTProperty
  rw [Set.mem_iUnion]
  simp
  use σ

/-!
Now we will prove a theorem about **Finite Trace Inclusion and Safety Properties**.
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
    simp [Satisfaction.Satisfies] at h₁
    have h₂ := finite_traces_are_prefixes TSwts₁
    have h₃ := finite_traces_are_prefixes TSwts₂
    have h₄ : prefLTProperty (TracesWTS TSwts₁) ⊆ prefLTProperty (closureLTProperty (TracesWTS TSwts₂)) := by
      rw [Set.subset_def]
      intro ω hω
      unfold prefLTProperty at hω
      rw [Set.mem_iUnion] at hω
      obtain ⟨σ, hσ, hω⟩ := hω
      simp at hω
      obtain ⟨hω₁, hω₃⟩ := hω
      obtain ⟨hω₁, hω₂⟩ := hω₁
      rw [← hω₂] at hω₃
      apply h₁ at hω₁
      unfold prefLTProperty
      rw [Set.mem_iUnion]
      use σ
      simp
      exact ⟨hω₁, hω₃⟩
    have h₅ := prefix_of_closure_is_prefix (TracesWTS TSwts₂)

    rw [h₂, h₃]
    simp
    intro t
    intro ht
    apply h₄ at ht
    rw [← h₅]
    assumption

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
      simp
    )

theorem finite_trace_and_trace_equivalence {AP: Type} (TSwts : TransitionSystemWTS AP) (TS : TransitionSystem AP) (hfin : isFinite TS) : Traces TSwts.TS ⊆ Traces TS ↔ TracesFin TSwts.TS ⊆ TracesFin TS := by
  unfold isFinite at hfin
  constructor
  · intro h
    rw [finite_traces_are_prefixes]
    intro t ht
    unfold prefLTProperty at ht
    simp at ht
    obtain ⟨T, hT₁, hT₂⟩ := ht
    let T' := Trace.infinite T
    unfold TracesWTS at hT₁
    rw [Set.mem_iUnion] at hT₁
    simp at hT₁
    obtain ⟨s, hs, hT₁⟩ := hT₁
    have hT' : T' ∈ Traces TSwts.TS := by
      unfold Traces TracesFromState
      simp
      use s, hs
      unfold TraceFromPathFragmentSet
      simp
      unfold TracesFromInitialStateWTS at hT₁
      simp at hT₁
      obtain ⟨π, hπ, hT₁⟩ := hT₁
      use π, hπ
      unfold T' TraceFromPathFragment
      match π with
      | PathFragment.finite p =>
        unfold PathsFromState isMaximalPathFragment endStatePathFragment at hπ
        simp at hπ
        obtain ⟨hπ, _⟩ := hπ
        obtain ⟨_, hTS⟩ := TSwts
        specialize hTS (p.states (Fin.last p.n))
        contradiction
      | PathFragment.infinite p =>
        simp
        unfold TraceFromPathFromInitialStateWTS TraceFromPathWTS at hT₁
        simp at hT₁
        assumption

    apply h at hT'
    unfold TracesFin TracesFinFromState
    simp
    unfold Traces TracesFromState at hT'
    rw [Set.mem_iUnion] at hT'
    simp at hT'
    obtain ⟨s, hs, hT'⟩ := hT'
    use s, hs

    obtain ⟨π, hπ, hT'⟩ := hT'
    unfold PathsFinFromState
    simp
    match π with
    | PathFragment.finite p =>
      unfold T' TraceFromPathFragment at hT'
      simp at hT'
    | PathFragment.infinite p =>
      let πfin : FinitePathFragment TS := ⟨t.n, fun i => p.states i, by
        intro i
        have hv := p.valid i
        simp
        exact hv⟩
      use πfin
      unfold startStatePathFragment πfin
      simp
      constructor
      · unfold PathsFromState isMaximalPathFragment endStatePathFragment startStatePathFragment at hπ
        simp at hπ
        assumption
      · unfold FiniteTraceFromFinitePathFragment
        simp
        unfold pref Prefix at hT₂
        rw [Set.mem_def] at hT₂
        obtain ⟨n, hT₂⟩ := hT₂
        simp at hT₂
        obtain ⟨hn, hf⟩ := hT₂
        unfold T' TraceFromPathFragment InfiniteTraceFromInfinitePathFragment at hT'
        simp at hT'
        rw [hT'] at hf
        rw [← hn] at hf
        simp at hf
        rw [← hf]
  · sorry

end section
