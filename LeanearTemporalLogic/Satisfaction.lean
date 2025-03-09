import Mathlib
import LeanearTemporalLogic.LTL

/-!
We will define a satisfaction relation as a type class. This will allow us to define satisfaction for different types of models.
-/
class Satisfaction (α β : Type) where
  Satisfies : α → β → Prop

infixl:70 (priority := high) " ⊨ " => Satisfaction.Satisfies

/-!
A world is a sequence of states where each state is set of atomic propositions (that are considered true in that state).
-/
def World : Type := ℕ → Set AP

/-!
A suffix of a world w starting at index i is a world w' such that w'(j) = w(i+j) for all j. We will denote this by w[i...].
-/
def suffix (σ : World) (i : ℕ) : World := fun j => σ (i + j)

syntax:60 term "[" term "…]" : term
macro_rules
  | `($σ[$i…]) => `(suffix $σ $i)

/-!
A simple lemma for composition of suffixes.
-/
def suffix_composition (σ : World) (i j : ℕ) : σ[i…][j…] = σ[i+j…] := by
  funext k
  unfold suffix
  rw [Nat.add_assoc]

/-!
Now we define what it means for a world to satisfy an LTL formula.
-/
section
open LTLFormula

def world_satisfies_ltl (σ : World) : LTLFormula → Prop
  | ⊤ => true
  | LTLFormula.atom a => a ∈ σ 0
  | ¬ ψ => ¬ (world_satisfies_ltl σ ψ)
  | ϕ₁ ∧ ϕ₂ => (world_satisfies_ltl σ ϕ₁) ∧ (world_satisfies_ltl σ ϕ₂)
  | ◯ ψ => world_satisfies_ltl (σ[1…]) ψ
  | ϕ₁ 𝓤 ϕ₂ => ∃ (j: ℕ), ((world_satisfies_ltl (σ[j…]) ϕ₂) ∧ ∀ (k: ℕ), (k < j → world_satisfies_ltl (σ[k…]) ϕ₁))

instance : Satisfaction World LTLFormula := ⟨world_satisfies_ltl⟩

/-!
We will now show satisfaction for ♢ and □ operators.
-/
theorem world_satisfies_eventually (σ : World) (ϕ : LTLFormula) : (σ ⊨ (♢ ϕ)) ↔ ∃ (i: ℕ), ((σ[i…]) ⊨ ϕ) := by
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

theorem world_satisfies_always (σ : World) (ϕ : LTLFormula) : (σ ⊨ (□ ϕ)) ↔ ∀ (i: ℕ), ((σ[i…]) ⊨ ϕ) := by
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

theorem world_satisfies_always_eventually (σ : World) (ϕ : LTLFormula) : (σ ⊨ (□ ♢ ϕ)) ↔ ∀ (i: ℕ), ∃ (j: ℕ), ((σ[i+j…]) ⊨ ϕ) := sorry

theorem world_satisfies_eventually_always (σ : World) (ϕ : LTLFormula) : (σ ⊨ (♢ □ ϕ)) ↔ ∃ (i: ℕ), ∀ (j: ℕ), ((σ[i+j…]) ⊨ ϕ) := sorry


/-!
We now define the set of worlds that satisfy a given LTL formula.
-/
def Worlds (ϕ : LTLFormula) : Set World := fun σ => σ ⊨ ϕ

end section
