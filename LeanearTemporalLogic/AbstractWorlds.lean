import Mathlib

def AbstractWorld (AP: Type) : Type := ℕ → Set AP

structure AbstractFiniteWorld (AP: Type) where
  n : ℕ
  f : Fin (n + 1) → Set AP
