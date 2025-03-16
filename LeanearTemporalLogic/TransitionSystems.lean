import Mathlib

/-!
Now we define a transition system, which is a tuple `(S, Act, ⟶, I, L)`, parameterized by a set `AP` of atomic propositions, where
- `S` is a set of states
- `Act` is a set of actions (or transitions)
- `Trans ⊆ S × Act × S` is a transition relation
- `I ⊆ S` is a set of initial states
- `L : S → 2^AP` is a labeling function
-/
structure TransitionSystem (AP: Type) where
  S : Type
  Act : Type
  Trans: S → Act → S → Prop
  I : S → Prop
  L : S → Set AP

namespace TransitionSystem

/-!
A finite transition system is a transition system where `S`, `Act`, and `AP` are finite sets.
-/
def isFinite (AP: Type) (TS : TransitionSystem AP) : Prop :=
  Nonempty (Fintype TS.S) ∧ Nonempty (Fintype TS.Act) ∧ Nonempty (Fintype AP)

/-!
Now we will define the notion of direct (α-) successors and (α-) predecessors in a transition system.
-/
def PostAction {AP: Type} {TS : TransitionSystem AP} (s : TS.S) (α : TS.Act) : Set TS.S :=
  { s' | TS.Trans s α s' }

def Post {AP: Type} {TS : TransitionSystem AP} (s : TS.S) : Set TS.S := ⋃ α, PostAction s α

def PreAction {AP: Type} {TS : TransitionSystem AP} (s : TS.S) (α : TS.Act) : Set TS.S :=
  { s' | TS.Trans s' α s }

def Pre {AP: Type} {TS : TransitionSystem AP} (s : TS.S) : Set TS.S := ⋃ α, PreAction s α

def PostActionSet {AP: Type} {TS : TransitionSystem AP} (C : Set TS.S) (α : TS.Act) : Set TS.S :=
  ⋃ s ∈ C, PostAction s α

def PostSet {AP: Type} {TS : TransitionSystem AP} (C : Set TS.S) : Set TS.S := ⋃ s ∈ C, Post s

def PreActionSet {AP: Type} {TS : TransitionSystem AP} (C : Set TS.S) (α : TS.Act) : Set TS.S :=
  ⋃ s ∈ C, PreAction s α

def PreSet {AP: Type} {TS : TransitionSystem AP} (C : Set TS.S) : Set TS.S := ⋃ s ∈ C, Pre s

/-!
Terminal states have no successors.
-/
def isTerminalState {AP: Type} {TS : TransitionSystem AP} (s : TS.S) : Prop := Post s = ∅

def hasNoTerminalStates {AP: Type} (TS : TransitionSystem AP) : Prop := ∀ s : TS.S, ¬ isTerminalState s

/-!
Execution fragments can be finite or infinite alternating sequences of states and actions, ending in a state.
-/
structure FiniteExecutionFragment {AP: Type} (TS: TransitionSystem AP) (n : ℕ) where
  states : Fin (n + 1) → TS.S
  actions : Fin n → TS.Act
  valid : ∀ (i: Fin n), TS.Trans (states i) (actions i) (states (i + 1))

structure InfiniteExecutionFragment {AP: Type} (TS: TransitionSystem AP) where
  states : ℕ → TS.S
  actions : ℕ → TS.Act
  valid: ∀ (i: ℕ), TS.Trans (states i) (actions i) (states (i + 1))

inductive ExecutionFragment {AP: Type} (TS: TransitionSystem AP) : Type
  | finite {n : ℕ} (e : FiniteExecutionFragment TS n)
  | infinite (e : InfiniteExecutionFragment TS)

/-!
Some helpful functions for working with execution fragments.
-/
def startStateExecutionFragment {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : TS.S :=
  match e with
  | ExecutionFragment.finite e => e.states 0
  | ExecutionFragment.infinite e => e.states 0

def endStateExecutionFragment {AP: Type} {TS : TransitionSystem AP} {n : ℕ} (e: FiniteExecutionFragment TS n) : TS.S := e.states (Fin.last n)

def isFiniteExecutionFragment {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : Prop := match e with
  | ExecutionFragment.finite _ => True
  | _ => False

def isInfiniteExecutionFragment {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : Prop := match e with
  | ExecutionFragment.infinite _ => True
  | _ => False

/-!
A *maximal* execution fragment is either finite and ending in a terminal state, or infinite.
-/
def isMaximalExecutionFragment {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : Prop :=
  match e with
  | ExecutionFragment.finite e => isTerminalState (endStateExecutionFragment e)
  | _ => True

/-!
For a transition system without terminal states, maximal execution fragments coincide with infinite execution fragments.
-/
theorem maximalIffInfiniteExecutionFragment {AP: Type} {TS : TransitionSystem AP} (h : hasNoTerminalStates TS) (e: ExecutionFragment TS) : isMaximalExecutionFragment e ↔ isInfiniteExecutionFragment e := by
  unfold isInfiniteExecutionFragment
  unfold isMaximalExecutionFragment
  unfold hasNoTerminalStates at h
  constructor
  · intro hmax
    cases e with
    | finite e =>
      simp
      simp at hmax
      specialize h (endStateExecutionFragment e)
      contradiction
    | infinite e =>
      simp
  · intro hinf
    cases e with
    | finite e =>
      simp
      simp at hinf
    | infinite e =>
      simp


/-!
An *initial* execution fragment is one that starts in an initial state.
-/
def isInitialExecutionFragment {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : Prop :=
  TS.I (startStateExecutionFragment e)

/-!
An *execution* of a transition system is an initial, maximal execution fragment.
-/
def isExecution {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : Prop :=
  isInitialExecutionFragment e ∧ isMaximalExecutionFragment e

/-!
A *reachable* state is one that appears at the end of an initial, finite execution fragment.
We wil define the set of all reachable states.
-/
def isReachableState {AP: Type} {TS : TransitionSystem AP} (s: TS.S) : Prop :=
  ∃ (n: ℕ) (e: FiniteExecutionFragment TS n), isInitialExecutionFragment (ExecutionFragment.finite e) ∧ endStateExecutionFragment e = s

def Reach {AP: Type} (TS: TransitionSystem AP) : Set TS.S := { s | isReachableState s }

/-!
It is usually easier to work with **Path Fragments** than with **Execution Fragments**.
-/
structure FinitePathFragment {AP: Type} (TS: TransitionSystem AP) (n : ℕ) where
  states : Fin (n + 1) → TS.S
  valid : ∀ (i: Fin n), states i ∈ Post (states (i + 1))

structure InfinitePathFragment {AP: Type} (TS: TransitionSystem AP) where
  states : ℕ → TS.S
  valid: ∀ (i: ℕ), states i ∈ Post (states (i + 1))

inductive PathFragment {AP: Type} (TS: TransitionSystem AP) : Type
  | finite {n : ℕ} (p : FinitePathFragment TS n)
  | infinite (p : InfinitePathFragment TS)

/-!
Some helpful functions for working with path fragments.
-/
def getPathState {AP: Type} {TS : TransitionSystem AP} (π : PathFragment TS) (i: ℕ) : Option TS.S :=
  match π with
  | @PathFragment.finite _ _ n π => if i < n then some (π.states i) else none
  | PathFragment.infinite π => some (π.states i)

def startStatePathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : TS.S :=
  match π with
  | PathFragment.finite e => e.states 0
  | PathFragment.infinite e => e.states 0

def endStatePathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Option TS.S :=
  match π with
  | @PathFragment.finite _ _ n π => π.states (Fin.last n)
  | PathFragment.infinite _ => none

def lengthPathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Option ℕ :=
  match π with
  | @PathFragment.finite _ _ n _ => n
  | PathFragment.infinite _ => none

def isFinitePathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Prop := match π with
  | PathFragment.finite _ => True
  | _ => False

def isInfinitePathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Prop := match π with
  | PathFragment.infinite _ => True
  | _ => False

/-!
A *maximal* path fragment is either finite and ending in a terminal state, or infinite.
A *initial* path fragment is one that starts in an initial state.
-/
def isMaximalPathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Prop :=
  match (endStatePathFragment π) with
  | some s => isTerminalState s
  | none => True

/-!
Similar to execution fragments, maximal path fragments coincide with infinite path fragments in transition systems without terminal states.
-/
theorem maximalIffInfinitePathFragment {AP: Type} {TS : TransitionSystem AP} (h : hasNoTerminalStates TS) (π: PathFragment TS) : isMaximalPathFragment π ↔ isInfinitePathFragment π := by
  unfold isMaximalPathFragment
  unfold isInfinitePathFragment
  unfold endStatePathFragment
  unfold hasNoTerminalStates at h
  constructor
  · intro hmax
    cases π with
    | @finite n π =>
      simp
      simp at hmax
      specialize h (π.states (Fin.last n))
      contradiction
    | infinite π =>
      simp
  · intro hinf
    cases π with
    | finite π =>
      simp
      simp at hinf
    | infinite π =>
      simp

def isInitialPathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Prop := TS.I (startStatePathFragment π)

/-!
A *path* is an initial, maximal path fragment.
-/
def isPath {AP: Type} {TS : TransitionSystem AP} (e: PathFragment TS) : Prop :=
  isInitialPathFragment e ∧ isMaximalPathFragment e

def Paths {AP: Type} (TS: TransitionSystem AP) : Set (PathFragment TS) := { e | isPath e }

def PathsFin {AP: Type} (TS: TransitionSystem AP) : Set (PathFragment TS) := { e | isInitialPathFragment e ∧ isFinitePathFragment e }

/-!
*Paths* can also originate from a given state.
-/
def PathsFromState {AP: Type} {TS : TransitionSystem AP} (s: TS.S) : Set (PathFragment TS) :=
  { π | isMaximalPathFragment π ∧ startStatePathFragment π = s }

def PathsFinFromState {AP: Type} {TS : TransitionSystem AP} (s: TS.S) : Set (PathFragment TS) :=
  { π | isFinitePathFragment π ∧ startStatePathFragment π = s }

/-!
The *trace* of a path fragment is its projection onto 2^AP.
-/
def FiniteTrace (AP: Type) (n : ℕ) := Fin (n + 1) → Set AP

def InfiniteTrace (AP: Type) := ℕ → Set AP

inductive Trace (AP: Type) : Type
  | finite {n : ℕ} (trace : FiniteTrace AP n)
  | infinite (trace : InfiniteTrace AP)

def FiniteTraceFromFinitePathFragment {AP: Type} {TS : TransitionSystem AP} {n: ℕ} (π: FinitePathFragment TS n) : FiniteTrace AP n :=
  fun i ↦ TS.L (π.states i)

def InfiniteTraceFromInfinitePathFragment {AP: Type} {TS : TransitionSystem AP} (π: InfinitePathFragment TS) : InfiniteTrace AP :=
  fun i ↦ TS.L (π.states i)

def TraceFromPathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Trace AP :=
  match π with
  | PathFragment.finite π => Trace.finite (FiniteTraceFromFinitePathFragment π)
  | PathFragment.infinite π => Trace.infinite (InfiniteTraceFromInfinitePathFragment π)

def TraceFromPathFragmentSet {AP: Type} {TS : TransitionSystem AP} (P : Set (PathFragment TS)) : Set (Trace AP) :=
  { trace | ∃ π ∈ P, trace = TraceFromPathFragment π }

def TracesFromState {AP: Type} {TS : TransitionSystem AP} (s: TS.S) : Set (Trace AP) :=
  TraceFromPathFragmentSet (PathsFromState s)

def TracesFinFromState {AP: Type} {TS : TransitionSystem AP} (s: TS.S) : Set (Trace AP) :=
  TraceFromPathFragmentSet (PathsFinFromState s)

def Traces {AP: Type} (TS: TransitionSystem AP) : Set (Trace AP) :=
  ⋃ s ∈ {s | TS.I s}, TracesFromState s

def TracesFin {AP: Type} (TS: TransitionSystem AP) : Set (Trace AP) :=
  ⋃ s ∈ {s | TS.I s}, TracesFinFromState s

/-!
We will specifically be interested in Transition Systems with no terminal states. We will define some structures and functions to make it easier to work with them.
-/
structure TransitionSystemWithoutTerminalStates (AP: Type) where
  TS: TransitionSystem AP
  h: hasNoTerminalStates TS

abbrev TransitionSystemWTS := TransitionSystemWithoutTerminalStates

/-!
Transition systems without terminal states have only infinite (paths and) traces. We can use this to simplify some definitions.
-/
def TracesFromPathsFromStateWTS {AP: Type} (TSwts: TransitionSystemWTS AP) (s: TSwts.TS.S) (p: PathFragment TSwts.TS) (h₁: p ∈ PathsFromState s) : InfiniteTrace AP := by
  rw [PathsFromState] at h₁
  rw [Set.mem_setOf] at h₁
  obtain ⟨h₃, h₄⟩ := h₁
  rw [maximalIffInfinitePathFragment TSwts.h] at h₃

  match p with
  | PathFragment.finite _ =>
      unfold isInfinitePathFragment at h₃
      simp at h₃
  | PathFragment.infinite π =>
      -- we can now construct the infinite trace
      have t : InfiniteTrace AP := InfiniteTraceFromInfinitePathFragment π
      exact t

def TracesFromStateWTS {AP: Type} {TSwts: TransitionSystemWTS AP} (s: TSwts.TS.S) : Set (InfiniteTrace AP) :=
  { t | ∃ (p: PathFragment TSwts.TS) (h: p ∈ PathsFromState s), t = TracesFromPathsFromStateWTS TSwts s p h }

def TracesWTS {AP: Type} (TSwts: TransitionSystemWTS AP) : Set (InfiniteTrace AP) :=
  ⋃ s ∈ {s | TSwts.TS.I s}, TracesFromStateWTS s

end TransitionSystem
