import LeanearTemporalLogic.AbstractWorlds

/-!
## Worlds and Traces

A world is an infinite sequence of states, each being a set of atomic propositions. Prefixes and suffixes of worlds are used to define temporal operators.
-/
/-- A `World` is an infinite sequence of sets of atomic propositions. -/
abbrev World := AbstractWorld
/-- A `FiniteWorld` is a finite sequence of sets of atomic propositions. -/
abbrev FiniteWorld := AbstractFiniteWorld

/--
A suffix of a world `w` starting at index `i` is a world `w'` such that `w'(j) = w(i+j)` for all `j`.
Denoted as `w[i…]`.
-/
def Suffix {AP: Type} (σ : World AP) (i : ℕ) : World AP := fun j => σ (i + j)

syntax:60 term "[" term "…]" : term
macro_rules
  | `($σ[$i…]) => `(Suffix $σ $i)

/--
Composition of suffixes: taking a suffix of a suffix is the same as taking a single suffix at the sum of the indices.
-/
theorem Suffix.composition {AP: Type} (σ : World AP) (i j : ℕ) : σ[i…][j…] = σ[i+j…] := by
  funext k
  unfold Suffix
  rw [Nat.add_assoc]

/--
The suffix at index 0 is the world itself.
-/
theorem Suffix.zero_identity {AP: Type} (σ : World AP) : σ[0…] = σ := by
  funext k
  unfold Suffix
  rw [Nat.zero_add]

/--
A prefix of a world is its initial segment of finite length `n`.
-/
def Prefix {AP: Type} (σ : World AP) (n: ℕ) : FiniteWorld AP := ⟨n, fun i => σ i⟩

/--
A prefix of a prefix, of length `m ≤ ω.n`.
-/
def PrefixOfPrefix {AP: Type} (ω : FiniteWorld AP) (m : ℕ) (h: m ≤ ω.n) : FiniteWorld AP := ⟨m, fun i => ω.f (Fin.castLE (by simp only [add_le_add_iff_right, h]) i)⟩

/--
The set of all prefixes of a world.
-/
def pref {AP: Type} (σ: World AP) : Set (FiniteWorld AP) := fun ω => ∃ (n: ℕ), ω = Prefix σ n
