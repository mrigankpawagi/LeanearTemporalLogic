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
-/

-- False
def False : LTLFormula := not True

-- Or
def or (ϕ ψ : LTLFormula) : LTLFormula := not (and (not ϕ) (not ψ))

-- Eventually
def eventually (ϕ : LTLFormula) : LTLFormula := LTLFormula.until True ϕ

-- Always
def always (ϕ : LTLFormula) : LTLFormula := not (eventually (not ϕ))

/-!
We will also define some syntactic sugar for the operators.
-/

-- `¬ϕ` for `not ϕ`
prefix:40 (priority := high) "¬ " => not

-- `ϕ ∧ ψ` for `and ϕ ψ`
infixl:50 (priority := high) " ∧ " => and

-- `ϕ ∨ ψ` for `or ϕ ψ`
infixl:50 (priority := high) " ∨ " => or

-- `◯ ϕ` for `next ϕ`
prefix:100 (priority := high) "◯ " => next

-- `ϕ 𝓤 ψ` for `until ϕ ψ`
infixl:60 (priority := high) " 𝓤 " => LTLFormula.until

-- `♢ ϕ` for `eventually ϕ`
prefix:100 (priority := high) "♢ " => eventually

-- `□ ϕ` for `always ϕ`
prefix:100 (priority := high) "□ " => always

-- `⊤` for `True` and `⊥` for `False`
notation "⊤" => True
notation "⊥" => False


/-!
The *length* of a formula is the number of operators in it. We count only the basic operators.
-/
def length : LTLFormula → Nat
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
  rw [or]
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
