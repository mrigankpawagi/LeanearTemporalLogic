import Mathlib

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
We will also define a *PL Formula* as an LTL formula without temporal operators.
-/

def isPLFormula {AP: Type} : LTLFormula AP → Prop
| .True => true
| .atom _ => true
| .not ϕ => isPLFormula ϕ
| .and ϕ ψ => isPLFormula ϕ ∧ isPLFormula ψ
| .next _ => false
| .until _ _ => false

structure PLFormula (AP: Type) where
  formula : LTLFormula AP
  h : isPLFormula formula

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
instance {AP: Type} : Not (PLFormula AP) := ⟨fun f ↦ ⟨LTLFormula.not f.formula, by
  obtain ⟨f', h⟩ := f
  simp
  rw [isPLFormula]
  exact h⟩⟩
prefix:50 (priority := high) "¬ " => Not.not

attribute [match_pattern] Not.not
@[simp] theorem not_def {AP: Type} (ϕ : LTLFormula AP) : (¬ ϕ) = LTLFormula.not ϕ := rfl
@[simp] theorem not_def_PL {AP: Type} (ϕ : PLFormula AP) : (¬ ϕ) = ⟨LTLFormula.not ϕ.formula, by
  obtain ⟨f, h⟩ := ϕ
  simp
  rw [isPLFormula]
  exact h⟩ := rfl

-- `ϕ ∧ ψ` for `and ϕ ψ`
class And (α : Type) where
  and : α → α → α

instance : And Prop := ⟨fun p q ↦ p ∧ q⟩
instance {AP: Type} : And (LTLFormula AP) := ⟨LTLFormula.and⟩
instance {AP: Type} : And (PLFormula AP) := ⟨fun f g ↦ ⟨LTLFormula.and f.formula g.formula, by
  obtain ⟨f', hf⟩ := f
  obtain ⟨g', hg⟩ := g
  simp
  rw [isPLFormula]
  constructor <;> assumption⟩⟩
infixl:65 (priority := high) " ∧ " => And.and

attribute [match_pattern] And.and
@[simp] theorem and_def {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ ∧ ψ) = LTLFormula.and ϕ ψ := rfl
@[simp] theorem and_def_PL {AP: Type} (ϕ ψ : PLFormula AP) : (ϕ ∧ ψ) = ⟨LTLFormula.and ϕ.formula ψ.formula, by
  obtain ⟨f, hf⟩ := ϕ
  obtain ⟨g, hg⟩ := ψ
  simp
  rw [isPLFormula]
  constructor <;> assumption⟩ := rfl

-- `ϕ ∨ ψ` for `or ϕ ψ`
class Or (α : Type) where
  or : α → α → α

instance : Or Prop := ⟨fun p q ↦ p ∨ q⟩
instance {AP: Type} : Or (LTLFormula AP) := ⟨fun ϕ ψ ↦ ¬ ((¬ ϕ) ∧ (¬ ψ))⟩
instance {AP: Type} : Or (PLFormula AP) := ⟨fun f g ↦ ⟨¬ ((¬ f.formula) ∧ (¬ g.formula)), by
  obtain ⟨f', hf⟩ := f
  obtain ⟨g', hg⟩ := g
  simp
  rw [isPLFormula]
  constructor <;> assumption⟩⟩
infixl:65 (priority := high) " ∨ " => Or.or
def or {AP: Type} (ϕ ψ : LTLFormula AP) : LTLFormula AP := Or.or ϕ ψ
def or_PL {AP: Type} (ϕ ψ : PLFormula AP) : PLFormula AP := Or.or ϕ ψ

attribute [match_pattern] Or.or
@[simp] theorem or_def {AP: Type} (ϕ ψ : LTLFormula AP) : (ϕ ∨ ψ) = (¬ ((¬ ϕ) ∧ (¬ ψ))) := rfl
@[simp] theorem or_def_PL {AP: Type} (ϕ ψ : PLFormula AP) : (ϕ ∨ ψ) = ⟨¬ ((¬ ϕ.formula) ∧ (¬ ψ.formula)), by
  obtain ⟨f, hf⟩ := ϕ
  obtain ⟨g, hg⟩ := ψ
  simp
  rw [isPLFormula]
  constructor <;> assumption⟩ := rfl

-- `◯ ϕ` for `next ϕ`
prefix:65 (priority := high) "◯ " => next

-- `ϕ 𝓤 ψ` for `until ϕ ψ`
infixl:50 (priority := high) " 𝓤 " => LTLFormula.until

-- Eventually
-- `♢ ϕ` for `eventually ϕ`
def eventually {AP: Type} (ϕ : LTLFormula AP) : LTLFormula AP := LTLFormula.until True ϕ
prefix:65 (priority := high) "♢ " => eventually

-- Always
-- `□ ϕ` for `always ϕ`
def always {AP: Type} (ϕ : LTLFormula AP) : LTLFormula AP := not (eventually (not ϕ))
prefix:65 (priority := high) "□ " => always

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
def length_or {AP: Type} (ϕ ψ : LTLFormula AP) : length (ϕ ∨ ψ) = 4 + length ϕ + length ψ := by
  simp
  repeat rw [length]
  omega

def length_eventually {AP: Type} (ϕ : LTLFormula AP) : length (♢ ϕ) = 1 + length ϕ := rfl

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

/-!
We can also define the length of a PL formula by using the above definition.
-/
def length_PL {AP: Type} (ϕ : PLFormula AP) : PLFormula AP → ℕ := length ϕ.formula

def length_PL_or {AP: Type} (ϕ ψ : PLFormula AP) : length_PL (ϕ ∨ ψ) = 4 + length_PL ϕ + length_PL ψ := by
  repeat rw [length_PL]
  simp only [Or.or]
  have h := length_or ϕ.formula ψ.formula
  simp only [Or.or] at h
  rw [h]
  simp

end LTLFormula
