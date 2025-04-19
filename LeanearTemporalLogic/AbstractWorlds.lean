/-
# AbstractWorlds

This module provides abstract representations of "worlds" for Linear Temporal Logic (LTL) and related formalisms.
A world is modeled as a sequence of sets of atomic propositions, representing the evolution of truth assignments over time.
We also provide a structure for finite worlds, useful for reasoning about bounded intervals of time.
-/

import Mathlib

def AbstractWorld (AP: Type) : Type := ℕ → Set AP

structure AbstractFiniteWorld (AP: Type) where
  n : ℕ
  f : Fin (n + 1) → Set AP
