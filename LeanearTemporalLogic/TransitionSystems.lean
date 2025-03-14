import Mathlib

/-!
Now we define a transition system, which is a tuple `(S, Act, ⟶, I, AP, L)`, where
- `S` is a set of states
- `Act` is a set of actions (or transitions)
- `Trans ⊆ S × Act × S` is a transition relation
- `I ⊆ S` is a set of initial states
- `AP` is a set of atomic propositions
- `L : S → 2^AP` is a labeling function
-/
structure TransitionSystem where
  S : Type
  Act : Type
  Trans: S → Act → S → Prop
  I : S → Prop
  AP : Type
  L : S → Set AP

namespace TransitionSystem

/-!
A finite transition system is a transition system where `S`, `Act`, and `AP` are finite sets.
-/
def isFinite (TS : TransitionSystem) : Prop :=
  Nonempty (Fintype TS.S) ∧ Nonempty (Fintype TS.Act) ∧ Nonempty (Fintype TS.AP)

/-!
Now we will define the notion of direct (α-) successors and (α-) predecessors in a transition system.
-/
def PostAction {TS : TransitionSystem} (s : TS.S) (α : TS.Act) : Set TS.S :=
  { s' | TS.Trans s α s' }

def Post {TS : TransitionSystem} (s : TS.S) : Set TS.S := ⋃ α, PostAction s α

def PreAction {TS : TransitionSystem} (s : TS.S) (α : TS.Act) : Set TS.S :=
  { s' | TS.Trans s' α s }

def Pre {TS : TransitionSystem} (s : TS.S) : Set TS.S := ⋃ α, PreAction s α

def PostActionSet {TS : TransitionSystem} (C : Set TS.S) (α : TS.Act) : Set TS.S :=
  ⋃ s ∈ C, PostAction s α

def PostSet {TS : TransitionSystem} (C : Set TS.S) : Set TS.S := ⋃ s ∈ C, Post s

def PreActionSet {TS : TransitionSystem} (C : Set TS.S) (α : TS.Act) : Set TS.S :=
  ⋃ s ∈ C, PreAction s α

def PreSet {TS : TransitionSystem} (C : Set TS.S) : Set TS.S := ⋃ s ∈ C, Pre s

/-!
Terminal states have no successors.
-/
def isTerminalState {TS : TransitionSystem} (s : TS.S) : Prop := Post s = ∅

def hasNoTerminalStates (TS : TransitionSystem) : Prop := ∀ s : TS.S, ¬ isTerminalState s

/-!
Execution fragments can be finite or infinite alternating sequences of states and actions, ending in a state.
-/
structure FiniteExecutionFragment (TS: TransitionSystem) (n : ℕ) where
  states : Fin (n + 1) → TS.S
  actions : Fin n → TS.Act
  valid : ∀ (i: Fin n), TS.Trans (states i) (actions i) (states (i + 1))

structure InfiniteExecutionFragment (TS: TransitionSystem) where
  states : ℕ → TS.S
  actions : ℕ → TS.Act
  valid: ∀ (i: ℕ), TS.Trans (states i) (actions i) (states (i + 1))

inductive ExecutionFragment (TS: TransitionSystem) : Type
  | finite {n : ℕ} (e : FiniteExecutionFragment TS n)
  | infinite (e : InfiniteExecutionFragment TS)

/-!
Some helpful functions for working with execution fragments.
-/
def startStateExecutionFragment {TS : TransitionSystem} (e: ExecutionFragment TS) : TS.S :=
  match e with
  | ExecutionFragment.finite e => e.states 0
  | ExecutionFragment.infinite e => e.states 0

def endStateExecutionFragment {TS : TransitionSystem} {n : ℕ} (e: FiniteExecutionFragment TS n) : TS.S := e.states (Fin.last n)

def isFiniteExecutionFragment {TS : TransitionSystem} (e: ExecutionFragment TS) : Prop := match e with
  | ExecutionFragment.finite _ => True
  | _ => False

def isInfiniteExecutionFragment {TS : TransitionSystem} (e: ExecutionFragment TS) : Prop := match e with
  | ExecutionFragment.infinite _ => True
  | _ => False

/-!
A *maximal* execution fragment is either finite and ending in a terminal state, or infinite.
-/
def isMaximalExecutionFragment {TS : TransitionSystem} (e: ExecutionFragment TS) : Prop :=
  match e with
  | ExecutionFragment.finite e => isTerminalState (endStateExecutionFragment e)
  | _ => True

/-!
For a transition system without terminal states, maximal execution fragments coincide with infinite execution fragments.
-/
theorem maximalIffInfiniteExecutionFragment {TS : TransitionSystem} (h : hasNoTerminalStates TS) (e: ExecutionFragment TS) : isMaximalExecutionFragment e ↔ isInfiniteExecutionFragment e := by
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
def isInitialExecutionFragment {TS : TransitionSystem} (e: ExecutionFragment TS) : Prop :=
  TS.I (startStateExecutionFragment e)

/-!
An *execution* of a transition system is an initial, maximal execution fragment.
-/
def isExecution {TS : TransitionSystem} (e: ExecutionFragment TS) : Prop :=
  isInitialExecutionFragment e ∧ isMaximalExecutionFragment e

/-!
A *reachable* state is one that appears at the end of an initial, finite execution fragment.
We wil define the set of all reachable states.
-/
def isReachableState {TS : TransitionSystem} (s: TS.S) : Prop :=
  ∃ (n: ℕ) (e: FiniteExecutionFragment TS n), isInitialExecutionFragment (ExecutionFragment.finite e) ∧ endStateExecutionFragment e = s

def Reach (TS: TransitionSystem) : Set TS.S := { s | isReachableState s }

/-!
It is usually easier to work with **Path Fragments** than with **Execution Fragments**.
-/
structure FinitePathFragment (TS: TransitionSystem) (n : ℕ) where
  states : Fin (n + 1) → TS.S
  valid : ∀ (i: Fin n), states i ∈ Post (states (i + 1))

structure InfinitePathFragment (TS: TransitionSystem) where
  states : ℕ → TS.S
  valid: ∀ (i: ℕ), states i ∈ Post (states (i + 1))

inductive PathFragment (TS: TransitionSystem) : Type
  | finite {n : ℕ} (p : FinitePathFragment TS n)
  | infinite (p : InfinitePathFragment TS)

/-!
Some helpful functions for working with path fragments.
-/
def getPathState {TS : TransitionSystem} (π : PathFragment TS) (i: ℕ) : Option TS.S :=
  match π with
  | @PathFragment.finite TS n π => if i < n then some (π.states i) else none
  | PathFragment.infinite π => some (π.states i)

def startStatePathFragment {TS : TransitionSystem} (π: PathFragment TS) : TS.S :=
  match π with
  | PathFragment.finite e => e.states 0
  | PathFragment.infinite e => e.states 0

def endStatePathFragment {TS : TransitionSystem} (π: PathFragment TS) : Option TS.S :=
  match π with
  | @PathFragment.finite TS n π => π.states (Fin.last n)
  | PathFragment.infinite _ => none

def lengthPathFragment {TS : TransitionSystem} (π: PathFragment TS) : Option ℕ :=
  match π with
  | @PathFragment.finite TS n _ => n
  | PathFragment.infinite _ => none

def isFinitePathFragment {TS : TransitionSystem} (π: PathFragment TS) : Prop := match π with
  | PathFragment.finite _ => True
  | _ => False

def isInfinitePathFragment {TS : TransitionSystem} (π: PathFragment TS) : Prop := match π with
  | PathFragment.infinite _ => True
  | _ => False

/-!
A *maximal* path fragment is either finite and ending in a terminal state, or infinite.
A *initial* path fragment is one that starts in an initial state.
-/
def isMaximalPathFragment {TS : TransitionSystem} (π: PathFragment TS) : Prop :=
  match (endStatePathFragment π) with
  | some s => isTerminalState s
  | none => True

/-!
Similar to execution fragments, maximal path fragments coincide with infinite path fragments in transition systems without terminal states.
-/
theorem maximalIffInfinitePathFragment {TS : TransitionSystem} (h : hasNoTerminalStates TS) (π: PathFragment TS) : isMaximalPathFragment π ↔ isInfinitePathFragment π := by
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

def isInitialPathFragment {TS : TransitionSystem} (π: PathFragment TS) : Prop := TS.I (startStatePathFragment π)

/-!
A *path* is an initial, maximal path fragment.
-/
def isPath {TS : TransitionSystem} (e: PathFragment TS) : Prop :=
  isInitialPathFragment e ∧ isMaximalPathFragment e

def Paths (TS: TransitionSystem) : Set (PathFragment TS) := { e | isPath e }

def PathsFin (TS: TransitionSystem) : Set (PathFragment TS) := { e | isInitialPathFragment e ∧ isFinitePathFragment e }

/-!
*Paths* can also originate from a given state.
-/
def PathsFromState {TS : TransitionSystem} (s: TS.S) : Set (PathFragment TS) :=
  { π | isMaximalPathFragment π ∧ startStatePathFragment π = s }

def PathsFinFromState {TS : TransitionSystem} (s: TS.S) : Set (PathFragment TS) :=
  { π | isFinitePathFragment π ∧ startStatePathFragment π = s }

/-!
The *trace* of a path fragment is its projection onto 2^AP.
-/
def FiniteTrace (TS: TransitionSystem) (n : ℕ) := Fin (n + 1) → Set TS.AP

def InfiniteTrace (TS: TransitionSystem) := ℕ → Set TS.AP

inductive Trace (TS: TransitionSystem) : Type
  | finite {n : ℕ} (trace : FiniteTrace TS n)
  | infinite (trace : InfiniteTrace TS)

def FiniteTraceFromFinitePathFragment {TS : TransitionSystem} {n: ℕ} (π: FinitePathFragment TS n) : FiniteTrace TS n :=
  fun i ↦ TS.L (π.states i)

def InfiniteTraceFromInfinitePathFragment {TS : TransitionSystem} (π: InfinitePathFragment TS) : InfiniteTrace TS :=
  fun i ↦ TS.L (π.states i)

def TraceFromPathFragment {TS : TransitionSystem} (π: PathFragment TS) : Trace TS :=
  match π with
  | PathFragment.finite π => Trace.finite (FiniteTraceFromFinitePathFragment π)
  | PathFragment.infinite π => Trace.infinite (InfiniteTraceFromInfinitePathFragment π)

def TraceFromPathFragmentSet {TS : TransitionSystem} (P : Set (PathFragment TS)) : Set (Trace TS) :=
  { trace | ∃ π ∈ P, trace = TraceFromPathFragment π }

def TracesFromState {TS : TransitionSystem} (s: TS.S) : Set (Trace TS) :=
  TraceFromPathFragmentSet (PathsFromState s)

def TracesFinFromState {TS : TransitionSystem} (s: TS.S) : Set (Trace TS) :=
  TraceFromPathFragmentSet (PathsFinFromState s)

def Traces (TS: TransitionSystem) : Set (Trace TS) :=
  ⋃ s ∈ {s | TS.I s}, TracesFromState s

def TracesFin (TS: TransitionSystem) : Set (Trace TS) :=
  ⋃ s ∈ {s | TS.I s}, TracesFinFromState s

/-!
We will specifically be interested in Transition Systems with no terminal states. We will define some structures and functions to make it easier to work with them.
-/
structure TransitionSystemWithoutTerminalStates where
  TS: TransitionSystem
  h: hasNoTerminalStates TS

abbrev TransitionSystemWTS := TransitionSystemWithoutTerminalStates

/-!
Transition systems without terminal states have only infinite (paths and) traces. We can use this to simplify some definitions.
-/
def TracesFromPathsFromStateWTS (TSwts: TransitionSystemWTS) (s: TSwts.TS.S) (p: PathFragment TSwts.TS) (h₁: p ∈ PathsFromState s) : InfiniteTrace TSwts.TS := by
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
      have t : InfiniteTrace TSwts.TS := InfiniteTraceFromInfinitePathFragment π
      exact t

def TracesFromStateWTS {TSwts: TransitionSystemWTS} (s: TSwts.TS.S) : Set (InfiniteTrace TSwts.TS) :=
  { t | ∃ (p: PathFragment TSwts.TS) (h: p ∈ PathsFromState s), t = TracesFromPathsFromStateWTS TSwts s p h }

def TracesWTS (TSwts: TransitionSystemWTS) : Set (InfiniteTrace TSwts.TS) :=
  ⋃ s ∈ {s | TSwts.TS.I s}, TracesFromStateWTS s

end TransitionSystem
