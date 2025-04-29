/-
# Satisfaction in Linear Temporal Logic

This module provides the formalization of the satisfaction relation between different objects in the context of Linear Temporal Logic (LTL) and Linear Time Properties (LT properties). Satisfaction also forms the basis for the notion of equivalence.

This module provides several results related to satisfaction and equivalence of these objects, including using them as the basis for characterizing certain kinds of objects.
-/
import Mathlib
import LeanearTemporalLogic.Worlds
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
