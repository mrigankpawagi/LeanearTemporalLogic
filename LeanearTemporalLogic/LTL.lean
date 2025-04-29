/-
# LTL

This module defines the syntax of Linear Temporal Logic (LTL), parameterized by the type of atomic propositions
that can be used in the formulas. It provides both the minimal syntax and convenient derived operators,
as well as functions for measuring formula complexity. It also defines Propositional Logic (PL) formulas
for completeness, since their satisfaction is a building block for satisfaction of LTL formulas.
-/

import Mathlib

set_option linter.flexible true

/-!
Now we define a *minimal* syntax for LTL formulas. We will add more operators later.
LTLformulae are parametrized by the type of atomic propositions.

Working with a smaller definition will make induction easier.
-/
inductive LTLFormula (AP: Type) : Type
| True
| atom (a : AP)
| not (ϕ : LTLFormula AP)
| and (ϕ ψ : LTLFormula AP)
| next (ϕ : LTLFormula AP)
| until (ϕ ψ : LTLFormula AP)

/-!
We will also define a *PL Formula* similar to an LTL formula without temporal operators.
`PLFormula AP` is the type of propositional logic formulas over atomic propositions of type `AP`.
It can be seen as a subset of `LTLFormula`, omitting temporal operators.
-/
inductive PLFormula (AP: Type) : Type
| True
| atom (a : AP)
| not (ϕ : PLFormula AP)
| and (ϕ ψ : PLFormula AP)

namespace LTLFormula

/-!
We will now add some more operators for convenience.
We will also define some syntactic sugar for the operators, avoiding clashes with the existing operators on `Prop`.
-/

-- `¬ϕ` for `not ϕ`
class Not (α: Type) where
  not : α → α

instance : Not Prop := ⟨fun p ↦ ¬ p⟩
instance {AP: Type} : Not (LTLFormula AP) := ⟨LTLFormula.not⟩
instance {AP: Type} : Not (PLFormula AP) := ⟨PLFormula.not⟩
prefix:50 (priority := high) "¬ " => Not.not
attribute [match_pattern] Not.not

-- `ϕ ∧ ψ` for `and ϕ ψ`
class And (α : Type) where
  and : α → α → α

instance : And Prop := ⟨fun p q ↦ p ∧ q⟩
instance {AP: Type} : And (LTLFormula AP) := ⟨LTLFormula.and⟩
instance {AP: Type} : And (PLFormula AP) := ⟨PLFormula.and⟩
infixl:65 (priority := high) " ∧ " => And.and
attribute [match_pattern] And.and

-- `ϕ ∨ ψ` for `or ϕ ψ`
class Or (α : Type) where
  or : α → α → α

instance : Or Prop := ⟨fun p q ↦ p ∨ q⟩
instance {AP: Type} : Or (LTLFormula AP) := ⟨fun ϕ ψ ↦ ¬ ((¬ ϕ) ∧ (¬ ψ))⟩
instance {AP: Type} : Or (PLFormula AP) := ⟨fun ϕ ψ ↦ ¬ ((¬ ϕ) ∧ (¬ ψ))⟩
infixl:65 (priority := high) " ∨ " => Or.or
attribute [match_pattern] Or.or

theorem or_def {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ ∨ ψ) = (¬ ((¬ ϕ) ∧ (¬ ψ))) := rfl

-- `◯ ϕ` for `next ϕ`
prefix:65 (priority := high) "◯ " => next

-- `ϕ 𝓤 ψ` for `until ϕ ψ`
infixl:50 (priority := high) " 𝓤 " => LTLFormula.until

-- Eventually
-- `♢ ϕ` for `eventually ϕ`
def eventually {AP: Type} (ϕ : LTLFormula AP) : LTLFormula AP := LTLFormula.until True ϕ
prefix:65 (priority := high) "♢ " => eventually

def eventually_def {AP: Type} (ϕ : LTLFormula AP) : (♢ ϕ) = (True 𝓤 ϕ) := rfl

-- Always
-- `□ ϕ` for `always ϕ`
def always {AP: Type} (ϕ : LTLFormula AP) : LTLFormula AP := not (eventually (not ϕ))
prefix:65 (priority := high) "□ " => always

def always_def {AP: Type} (ϕ : LTLFormula AP) : (□ ϕ) = (¬ ♢ (¬ ϕ)) := rfl

-- `⊤` for `True` and `⊥` for `False`
def False {AP: Type} : LTLFormula AP := not True
notation "⊤" => True
notation "⊥" => False

-- Weak Until
-- `ϕ 𝓦 ψ` for `weakuntil ϕ ψ`
def weakuntil {AP: Type} (ϕ ψ : LTLFormula AP) : LTLFormula AP := (ϕ 𝓤 ψ) ∨ (□ ϕ)
infixl:50 (priority := high) " 𝓦 " => weakuntil

/-!
The *length* of a formula is the number of operators in it. We count only the basic operators.
This can be used to reason about the structural complexity of formulas, which is useful in showing
the time complexity of model-checking algorithms.
-/
def length {AP: Type} : LTLFormula AP → ℕ
| ⊤ => 0
| atom _ => 0
| ¬ ϕ => 1 + length ϕ
| ϕ ∧ ψ => 1 + length ϕ + length ψ
| ◯ ϕ => 1 + length ϕ
| ϕ 𝓤 ψ => 1 + length ϕ + length ψ

/-!
We will define some lemmas to make it easier to calculate the length of a formula with other operators.
-/
@[simp]
def length_not {AP: Type} (ϕ : LTLFormula AP) : length (¬ ϕ) = 1 + length ϕ := rfl

@[simp]
def length_and {AP: Type} (ϕ ψ : LTLFormula AP) : length (ϕ ∧ ψ) = 1 + length ϕ + length ψ := rfl

@[simp]
def length_next {AP: Type} (ϕ : LTLFormula AP) : length (◯ ϕ) = 1 + length ϕ := rfl

@[simp]
def length_until {AP: Type} (ϕ ψ : LTLFormula AP) : length (ϕ 𝓤 ψ) = 1 + length ϕ + length ψ := rfl

@[simp]
def length_or {AP: Type} (ϕ ψ : LTLFormula AP) : length (ϕ ∨ ψ) = 4 + length ϕ + length ψ := by
  rw [or_def, length_not, length_and, length_not, length_not]
  omega

@[simp]
def length_eventually {AP: Type} (ϕ : LTLFormula AP) : length (♢ ϕ) = 1 + length ϕ := rfl

@[simp]
def length_always {AP: Type} (ϕ : LTLFormula AP) : length (□ ϕ) = 3 + length ϕ := by
  rw [always]
  rw [length, length_eventually, length]
  omega

example {AP: Type} : @length AP ⊤ = 0 := rfl
example {AP: Type} : @length AP ⊥ = 1 := rfl
example {AP: Type} (a : AP) : length (¬ atom a) = 1 := rfl
example {AP: Type} (a b : AP) : length ((◯ atom a) ∧ atom b) = 2 := rfl
example {AP: Type} (a b : AP) : length ((◯ atom a) ∨ atom b) = 5 := by
  rw [length_or]
  rfl

end LTLFormula

namespace PLFormula

/-!
Some lemmas to work with PL formulas.
-/
theorem or_def {AP: Type} (ϕ ψ : PLFormula AP) : (ϕ ∨ ψ) = (¬ ((¬ ϕ) ∧ (¬ ψ))) := rfl

/-!
Since PL Formulas can be seen as LTL Formulas without temporal operators, we will define a transformation from PLFormula to LTLFormula.
-/
def toLTLFormula {AP: Type} : PLFormula AP → LTLFormula AP
| PLFormula.True => ⊤
| PLFormula.atom a => LTLFormula.atom a
| PLFormula.not ϕ => ¬ (PLFormula.toLTLFormula ϕ)
| PLFormula.and ϕ ψ => (PLFormula.toLTLFormula ϕ) ∧ (PLFormula.toLTLFormula ψ)

@[simp]
def toLTLFormula_not {AP: Type} (ϕ : PLFormula AP) : toLTLFormula (¬ ϕ) = (¬ toLTLFormula ϕ) := rfl

@[simp]
def toLTLFormula_and {AP: Type} (ϕ ψ : PLFormula AP) : toLTLFormula (ϕ ∧ ψ) = toLTLFormula ϕ ∧ toLTLFormula ψ := rfl

@[simp]
def toLTLFormula_or {AP: Type} (ϕ ψ : PLFormula AP) : toLTLFormula (ϕ ∨ ψ) = toLTLFormula ϕ ∨ toLTLFormula ψ := by
  rw [or_def, toLTLFormula_not, toLTLFormula_and, toLTLFormula_not, toLTLFormula_not]
  rw [LTLFormula.or_def]

/-!
We can also define the length of a PL formula by using the above definition.
-/
def length {AP: Type} (ϕ: PLFormula AP) : ℕ := LTLFormula.length ϕ.toLTLFormula

@[simp]
def length_not {AP: Type} (ϕ : PLFormula AP) : length (¬ ϕ) = 1 + length ϕ := rfl

@[simp]
def length_and {AP: Type} (ϕ ψ : PLFormula AP) : length (ϕ ∧ ψ) = 1 + length ϕ + length ψ := rfl

@[simp]
def length_or {AP: Type} (ϕ ψ : PLFormula AP) : length (ϕ ∨ ψ) = 4 + length ϕ + length ψ := by
  rw [or_def, length_not, length_and, length_not, length_not]
  omega

end PLFormula
