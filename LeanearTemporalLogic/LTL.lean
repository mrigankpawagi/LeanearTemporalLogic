import Mathlib

/-!
We first define the set of propositional variables, i.e., **atomic propositions**.
-/
opaque AP : Type

/-!
Now we define a *minimal* syntax for LTL formulas. We will add more operators later.

Working with a smaller definition will make induction easier.
-/
inductive LTLFormula : Type
| True
| atom (a : AP)
| not (ϕ : LTLFormula)
| and (ϕ ψ : LTLFormula)
| next (ϕ : LTLFormula)
| until (ϕ ψ : LTLFormula)

namespace LTLFormula

/-!
We will now add some more operators for convenience.
We will also define some syntactic sugar for the operators, avoiding clashes with the existing operators on `Prop`.
-/

-- `¬ϕ` for `not ϕ`
class Not (α: Type) where
  not : α → α

instance : Not Prop := ⟨fun p ↦ ¬ p⟩
instance : Not LTLFormula := ⟨LTLFormula.not⟩
prefix:50 (priority := high) "¬ " => Not.not

attribute [match_pattern] Not.not
@[simp] theorem not_def (ϕ : LTLFormula) : (¬ ϕ) = LTLFormula.not ϕ := rfl

-- `ϕ ∧ ψ` for `and ϕ ψ`
class And (α : Type) where
  and : α → α → α

instance : And Prop := ⟨fun p q ↦ p ∧ q⟩
instance : And LTLFormula := ⟨LTLFormula.and⟩
infixl:65 (priority := high) " ∧ " => And.and

attribute [match_pattern] And.and
@[simp] theorem and_def (ϕ ψ : LTLFormula) : (ϕ ∧ ψ) = LTLFormula.and ϕ ψ := rfl

-- `ϕ ∨ ψ` for `or ϕ ψ`
class Or (α : Type) where
  or : α → α → α

instance : Or Prop := ⟨fun p q ↦ p ∨ q⟩
instance : Or LTLFormula := ⟨fun ϕ ψ ↦ ¬ ((¬ ϕ) ∧ (¬ ψ))⟩
infixl:65 (priority := high) " ∨ " => Or.or
def or (ϕ ψ : LTLFormula) : LTLFormula := Or.or ϕ ψ

attribute [match_pattern] Or.or
@[simp] theorem or_def (ϕ ψ : LTLFormula) : (ϕ ∨ ψ) = (¬ ((¬ ϕ) ∧ (¬ ψ))) := rfl

-- `◯ ϕ` for `next ϕ`
prefix:65 (priority := high) "◯ " => next

-- `ϕ 𝓤 ψ` for `until ϕ ψ`
infixl:50 (priority := high) " 𝓤 " => LTLFormula.until

-- Eventually
-- `♢ ϕ` for `eventually ϕ`
def eventually (ϕ : LTLFormula) : LTLFormula := LTLFormula.until True ϕ
prefix:65 (priority := high) "♢ " => eventually

-- Always
-- `□ ϕ` for `always ϕ`
def always (ϕ : LTLFormula) : LTLFormula := not (eventually (not ϕ))
prefix:65 (priority := high) "□ " => always

-- `⊤` for `True` and `⊥` for `False`
def False : LTLFormula := not True
notation "⊤" => True
notation "⊥" => False


/-!
The *length* of a formula is the number of operators in it. We count only the basic operators.
-/
def length : LTLFormula → ℕ
| ⊤ => 0
| atom _ => 0
| ¬ ϕ => 1 + length ϕ
| ϕ ∧ ψ => 1 + length ϕ + length ψ
| ◯ ϕ => 1 + length ϕ
| ϕ 𝓤 ψ => 1 + length ϕ + length ψ

/-!
We will define some lemmas to make it easier to calculate the length of a formula with other operators.
-/
def length_or (ϕ ψ : LTLFormula) : length (ϕ ∨ ψ) = 4 + length ϕ + length ψ := by
  simp
  repeat rw [length]
  omega

def length_eventually (ϕ : LTLFormula) : length (♢ ϕ) = 1 + length ϕ := rfl

def length_always (ϕ : LTLFormula) : length (□ ϕ) = 3 + length ϕ := by
  rw [always]
  rw [length, length_eventually, length]
  omega

example : length ⊤ = 0 := rfl
example : length ⊥ = 1 := rfl
example (a : AP) : length (¬ atom a) = 1 := rfl
example (a b : AP) : length ((◯ atom a) ∧ atom b) = 2 := rfl
example (a b : AP) : length ((◯ atom a) ∨ atom b) = 5 := by
  rw [length_or]
  rfl

end LTLFormula
