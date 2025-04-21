/-
# Transition Systems

This module formalizes *transition systems*, which in our context are discrete-time dynamical systems that evolve over time through transitions between states. Transition systems are a natural way to represent the behavior of programs and thus are an important abstraction in model-checking.

This module includes the basic defition of transition systems, along with definitions of several objects that arise out of transition systems, like executions, paths, and traces. This module also defines many properties on these objects as well functions for working with them.
-/
import Mathlib
import LeanearTemporalLogic.AbstractWorlds

/-
A transition system is a tuple `(S, Act, ⟶, I, L)`, parameterized by a set `AP` of atomic propositions, where
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

/--
A transition system is *finite* if its set of states, actions, and atomic propositions are all finite.
-/
def isFinite {AP: Type} (TS : TransitionSystem AP) : Prop :=
  Finite TS.S ∧ Finite TS.Act ∧ Finite AP

/--
The set of direct successors of a state `s` via action `α`.
-/
def PostAction {AP: Type} {TS : TransitionSystem AP} (s : TS.S) (α : TS.Act) : Set TS.S :=
  { s' | TS.Trans s α s' }

/--
The set of all direct successors of a state `s` (via any action).
These are also called α-successors.
-/
def Post {AP: Type} {TS : TransitionSystem AP} (s : TS.S) : Set TS.S := ⋃ α, PostAction s α

/--
The set of direct predecessors of a state `s` via action `α`.
-/
def PreAction {AP: Type} {TS : TransitionSystem AP} (s : TS.S) (α : TS.Act) : Set TS.S :=
  { s' | TS.Trans s' α s }

/--
The set of all direct predecessors of a state `s` (via any action).
These are also called α-predecessors.
-/
def Pre {AP: Type} {TS : TransitionSystem AP} (s : TS.S) : Set TS.S := ⋃ α, PreAction s α

/--
The set of direct successors (via action `α`) of a set of states `C`.
-/
def PostActionSet {AP: Type} {TS : TransitionSystem AP} (C : Set TS.S) (α : TS.Act) : Set TS.S :=
  ⋃ s ∈ C, PostAction s α

/--
The set of all direct successors of a set of states `C`.
-/
def PostSet {AP: Type} {TS : TransitionSystem AP} (C : Set TS.S) : Set TS.S := ⋃ s ∈ C, Post s

/--
The set of direct predecessors (via action `α`) of a set of states `C`.
-/
def PreActionSet {AP: Type} {TS : TransitionSystem AP} (C : Set TS.S) (α : TS.Act) : Set TS.S :=
  ⋃ s ∈ C, PreAction s α

/--
The set of all direct predecessors of a set of states `C`.
-/
def PreSet {AP: Type} {TS : TransitionSystem AP} (C : Set TS.S) : Set TS.S := ⋃ s ∈ C, Pre s

/--
A *terminal state* is a state with no successors.
-/
def isTerminalState {AP: Type} {TS : TransitionSystem AP} (s : TS.S) : Prop := Post s = ∅

/--
A transition system has *no terminal states* if none of its states is a terminal state. This definition is important since we will specifically work with such transition systems in many cases.
-/
def hasNoTerminalStates {AP: Type} (TS : TransitionSystem AP) : Prop := ∀ s : TS.S, ¬ isTerminalState s

/--
A *finite execution fragment* is a finite alternating sequence of states and actions, ending in a state, such that each transition is valid, i.e., each action in the sequence takes the preceding state to the following state.
-/
structure FiniteExecutionFragment {AP: Type} (TS: TransitionSystem AP) where
  n : ℕ
  states : Fin (n + 1) → TS.S
  actions : Fin n → TS.Act
  valid : ∀ (i: Fin n), TS.Trans (states i) (actions i) (states (i + 1))

/--
An *infinite execution fragment* is an infinite alternating sequence of states and actions, such that each transition is valid.
-/
structure InfiniteExecutionFragment {AP: Type} (TS: TransitionSystem AP) where
  states : ℕ → TS.S
  actions : ℕ → TS.Act
  valid: ∀ (i: ℕ), TS.Trans (states i) (actions i) (states (i + 1))

/--
An *execution fragment* is either a finite or infinite execution fragment.
-/
inductive ExecutionFragment {AP: Type} (TS: TransitionSystem AP) : Type
  | finite (e : FiniteExecutionFragment TS)
  | infinite (e : InfiniteExecutionFragment TS)

/--
The *start state* of an execution fragment.
-/
def startStateExecutionFragment {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : TS.S :=
  match e with
  | ExecutionFragment.finite e => e.states 0
  | ExecutionFragment.infinite e => e.states 0

/--
The *end state* of a finite execution fragment.
-/
def endStateExecutionFragment {AP: Type} {TS : TransitionSystem AP} (e: FiniteExecutionFragment TS) : TS.S := e.states (Fin.last e.n)

/--
Predicate for whether an execution fragment is *finite*.
-/
def isFiniteExecutionFragment {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : Prop := match e with
  | ExecutionFragment.finite _ => True
  | _ => False

/--
Predicate for whether an execution fragment is *infinite*.
-/
def isInfiniteExecutionFragment {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : Prop := match e with
  | ExecutionFragment.infinite _ => True
  | _ => False

/--
A *maximal* execution fragment is either infinite, or finite and ends in a terminal state.
-/
def isMaximalExecutionFragment {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : Prop :=
  match e with
  | ExecutionFragment.finite e => isTerminalState (endStateExecutionFragment e)
  | _ => True

/--
In a transition system without terminal states, maximal execution fragments are exactly the infinite ones.
-/
theorem maximalIffInfiniteExecutionFragment {AP: Type} {TS : TransitionSystem AP} (h : hasNoTerminalStates TS) (e: ExecutionFragment TS) : isMaximalExecutionFragment e ↔ isInfiniteExecutionFragment e := by
  unfold isInfiniteExecutionFragment
  unfold isMaximalExecutionFragment
  unfold hasNoTerminalStates at h
  constructor
  · intro hmax
    cases e with
    | finite e =>
      simp only
      simp only at hmax
      specialize h (endStateExecutionFragment e)
      contradiction
    | infinite e =>
      simp only
  · intro hinf
    cases e with
    | finite e =>
      simp only
      simp only at hinf
    | infinite e =>
      simp only

/--
An *initial* execution fragment is one that starts in an initial state.
-/
def isInitialExecutionFragment {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : Prop :=
  TS.I (startStateExecutionFragment e)

/--
An *execution* is an initial, maximal execution fragment.
-/
def isExecution {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : Prop :=
  isInitialExecutionFragment e ∧ isMaximalExecutionFragment e

/--
A *reachable state* is one that appears at the end of an initial, finite execution fragment.
-/
def isReachableState {AP: Type} {TS : TransitionSystem AP} (s: TS.S) : Prop :=
  ∃ (e: FiniteExecutionFragment TS), isInitialExecutionFragment (ExecutionFragment.finite e) ∧ endStateExecutionFragment e = s

/--
The set of all reachable states in a transition system.
-/
def Reach {AP: Type} (TS: TransitionSystem AP) : Set TS.S := { s | isReachableState s }

/-
It is usually easier to work with **Path Fragments** than with **Execution Fragments**.
-/

/--
A *finite path fragment* is a finite sequence of states such that each consecutive pair is related by a valid transition, i.e., there is an action in the transition system between the two states.
-/
structure FinitePathFragment {AP: Type} (TS: TransitionSystem AP) where
  n : ℕ
  states : Fin (n + 1) → TS.S
  valid : ∀ (i: Fin n), states (i + 1) ∈ Post (states i)

/--
An *infinite path fragment* is an infinite sequence of states such that each consecutive pair is related by a valid transition.
-/
structure InfinitePathFragment {AP: Type} (TS: TransitionSystem AP) where
  states : ℕ → TS.S
  valid: ∀ (i: ℕ), states (i + 1) ∈ Post (states i)

/--
A *path fragment* is either a finite or infinite path fragment.
-/
inductive PathFragment {AP: Type} (TS: TransitionSystem AP) : Type
  | finite (p : FinitePathFragment TS)
  | infinite (p : InfinitePathFragment TS)

/--
Get the state at index `i` in a path fragment. Returns `none` if `i` is out of bounds for finite path fragments.
-/
def getPathState {AP: Type} {TS : TransitionSystem AP} (π : PathFragment TS) (i: ℕ) : Option TS.S :=
  match π with
  | PathFragment.finite π => if i < π.n then some (π.states i) else none
  | PathFragment.infinite π => some (π.states i)

/--
The *start state* of a path fragment.
-/
def startStatePathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : TS.S :=
  match π with
  | PathFragment.finite e => e.states 0
  | PathFragment.infinite e => e.states 0

/--
The *end state* of a finite path fragment, or `none` if infinite.
-/
def endStatePathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Option TS.S :=
  match π with
  | PathFragment.finite π => π.states (Fin.last π.n)
  | PathFragment.infinite _ => none

/--
The length of a path fragment, or `none` if infinite.
-/
def lengthPathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Option ℕ :=
  match π with
  | PathFragment.finite π => π.n
  | PathFragment.infinite _ => none

/--
Predicate for whether a path fragment is *finite*.
-/
def isFinitePathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Prop := match π with
  | PathFragment.finite _ => True
  | _ => False

/--
Predicate for whether a path fragment is *infinite*.
-/
def isInfinitePathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Prop := match π with
  | PathFragment.infinite _ => True
  | _ => False

/--
Convert a finite execution fragment to a finite path fragment.
-/
def finiteExecutionFragmentToFinitePathFragment {AP: Type} {TS : TransitionSystem AP} (e: FiniteExecutionFragment TS) : FinitePathFragment TS := ⟨e.n, e.states, by
  intro i
  unfold Post
  unfold PostAction
  simp only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Set.mem_iUnion, Set.mem_setOf_eq]
  have h := e.valid i
  use e.actions i
  simp only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ] at h
  assumption⟩

/--
Convert an infinite execution fragment to an infinite path fragment.
-/
def infiniteExecutionFragmentToInfinitePathFragment {AP: Type} {TS : TransitionSystem AP} (e: InfiniteExecutionFragment TS) : InfinitePathFragment TS := ⟨e.states, by
  intro i
  unfold Post
  unfold PostAction
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  have h := e.valid i
  use e.actions i⟩

/--
Convert an execution fragment to a path fragment.
-/
def executionFragmentToPathFragment {AP: Type} {TS : TransitionSystem AP} (e: ExecutionFragment TS) : PathFragment TS :=
  match e with
  | ExecutionFragment.finite e => PathFragment.finite (finiteExecutionFragmentToFinitePathFragment e)
  | ExecutionFragment.infinite e => PathFragment.infinite (infiniteExecutionFragmentToInfinitePathFragment e)

/--
Convert a finite path fragment to a finite execution fragment.
This is noncomputable in general because the path fragment only tells us that valid transitions
exist, without given a concrete action for each transition. The set of possible actions at any
step may be infinite.
-/
noncomputable def finitePathFragmentToFiniteExecutionFragment {AP: Type} {TS : TransitionSystem AP} (π: FinitePathFragment TS) : FiniteExecutionFragment TS := ⟨π.n, π.states,
  fun i => by
    have h : π.states (i + 1) ∈ Post (π.states i) := π.valid i
    unfold Post PostAction at h
    simp only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Set.mem_iUnion, Set.mem_setOf_eq] at h
    let α: TS.Act := Exists.choose h
    let hα := Exists.choose_spec h
    exact α,
  by
    intro i
    have h : π.states (i + 1) ∈ Post (π.states i) := π.valid i
    unfold Post PostAction at h
    simp only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Set.mem_iUnion, Set.mem_setOf_eq] at h
    let hα := Exists.choose_spec h
    simp only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ]
    exact hα⟩

/--
Convert an infinite path fragment to an infinite execution fragment.
This is noncomputable in general because the set of possible actions at any step may be infinite.
-/
noncomputable def infinitePathFragmentToInfiniteExecutionFragment {AP: Type} {TS : TransitionSystem AP} (π: InfinitePathFragment TS) : InfiniteExecutionFragment TS := ⟨π.states,
  fun i => by
    have h : π.states (i + 1) ∈ Post (π.states i) := π.valid i
    unfold Post PostAction at h
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at h
    let α: TS.Act := Exists.choose h
    let hα := Exists.choose_spec h
    exact α,
  by
    intro i
    have h : π.states (i + 1) ∈ Post (π.states i) := π.valid i
    unfold Post PostAction at h
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at h
    let hα := Exists.choose_spec h
    simp only
    exact hα⟩

/--
Convert a path fragment to an execution fragment. This is noncomputable.
-/
noncomputable def pathFragmentToExecutionFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : ExecutionFragment TS :=
  match π with
  | PathFragment.finite π => ExecutionFragment.finite (finitePathFragmentToFiniteExecutionFragment π)
  | PathFragment.infinite π => ExecutionFragment.infinite (infinitePathFragmentToInfiniteExecutionFragment π)

/--
A *maximal* path fragment is either infinite, or finite and ends in a terminal state.
-/
def isMaximalPathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Prop :=
  match (endStatePathFragment π) with
  | some s => isTerminalState s
  | none => True

/--
In a transition system without terminal states, maximal path fragments are exactly the infinite ones.
-/
theorem maximalIffInfinitePathFragment {AP: Type} {TS : TransitionSystem AP} (h : hasNoTerminalStates TS) (π: PathFragment TS) : isMaximalPathFragment π ↔ isInfinitePathFragment π := by
  unfold isMaximalPathFragment
  unfold isInfinitePathFragment
  unfold endStatePathFragment
  unfold hasNoTerminalStates at h
  constructor
  · intro hmax
    cases π with
    | finite π =>
      simp only
      simp only at hmax
      specialize h (π.states (Fin.last π.n))
      contradiction
    | infinite π =>
      simp only
  · intro hinf
    cases π with
    | finite π =>
      simp only
      simp only at hinf
    | infinite π =>
      simp only

/--
An *initial* path fragment is one that starts in an initial state.
-/
def isInitialPathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Prop := TS.I (startStatePathFragment π)

/--
A *path* is an initial, maximal path fragment.
-/
def isPath {AP: Type} {TS : TransitionSystem AP} (e: PathFragment TS) : Prop :=
  isInitialPathFragment e ∧ isMaximalPathFragment e

/--
The set of all (finite or infinite) paths in a transition system.
-/
def Paths {AP: Type} (TS: TransitionSystem AP) : Set (PathFragment TS) := { e | isPath e }

/--
The set of all finite paths in a transition system.
-/
def PathsFin {AP: Type} (TS: TransitionSystem AP) : Set (PathFragment TS) := { e | isInitialPathFragment e ∧ isFinitePathFragment e }

/--
The set of all paths originating from a given state.
-/
def PathsFromState {AP: Type} {TS : TransitionSystem AP} (s: TS.S) : Set (PathFragment TS) :=
  { π | isMaximalPathFragment π ∧ startStatePathFragment π = s }

/--
The set of all finite paths originating from a given state.
-/
def PathsFinFromState {AP: Type} {TS : TransitionSystem AP} (s: TS.S) : Set (FinitePathFragment TS) :=
  { π | startStatePathFragment (PathFragment.finite π) = s }

/--
Every path is contained in the set of paths starting from its start state.
-/
theorem path_starts_from_startState {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) (h: π ∈ Paths TS)
: π ∈ PathsFromState (startStatePathFragment π) := by
  unfold PathsFromState
  simp only [Set.mem_setOf_eq, and_true]
  rw [Paths] at h
  simp only [Set.mem_setOf_eq] at h
  rw [isPath] at h
  obtain ⟨_, hmax⟩ := h
  exact hmax

/--
Given a transition system without terminal states and a state `s`, constructs an infinite sequence of states starting from `s`. This is noncomputable in general since the possible actions at any
step may be infinite.
-/
noncomputable def construct_pathStates_from_state_if_noTerminalState {AP: Type} {TS : TransitionSystem AP} (h: hasNoTerminalStates TS) (s: TS.S) : ℕ → TS.S
  | 0 => s
  | n + 1 => by
    unfold hasNoTerminalStates at h
    let prev := construct_pathStates_from_state_if_noTerminalState h s n
    specialize h prev
    unfold isTerminalState at h
    unfold Post at h
    unfold PostAction at h
    rw [Set.eq_empty_iff_forall_not_mem] at h
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_forall, not_not] at h
    let x := Exists.choose h

    have valid : x ∈ Post prev := by
      unfold Post PostAction
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      let hx := Exists.choose_spec h
      obtain ⟨α, h'⟩ := hx
      use α

    exact x

/--
In a transition system without terminal states, there is always a path originating from any state.
-/
theorem path_originates_from_state_if_noTerminalState {AP: Type} {TS : TransitionSystem AP} (h: hasNoTerminalStates TS) (s: TS.S) : ∃ π, π ∈ PathsFromState s := by
  unfold hasNoTerminalStates at h

  let π := PathFragment.infinite ⟨construct_pathStates_from_state_if_noTerminalState h s, by
    intro i
    simp only [construct_pathStates_from_state_if_noTerminalState]
    simp only [construct_pathStates_from_state_if_noTerminalState.proof_4]⟩

  use π
  unfold PathsFromState
  unfold isMaximalPathFragment
  unfold endStatePathFragment
  unfold startStatePathFragment
  unfold π
  simp only [Set.mem_setOf_eq, true_and]
  unfold construct_pathStates_from_state_if_noTerminalState
  simp only

/--
Concatenate a finite path fragment and an infinite path fragment, provided the end of the finite
path fragment matches the start of the infinite path fragment.
-/
def PathFragment.concatenate_finite_and_infinite {AP: Type} {TS : TransitionSystem AP} (π: FinitePathFragment TS) (π': InfinitePathFragment TS) (hcont : π.states (Fin.last π.n) = π'.states 0) : InfinitePathFragment TS := ⟨fun i => if i < π.n then π.states i else π'.states (i - π.n), by
  intro i
  simp only [Nat.cast_add, Nat.cast_one]
  if hi: i < π.n then
    simp only [hi, ↓reduceIte]
    if hii: i + 1 < π.n then
      simp only [hii, ↓reduceIte]
      have hv := π.valid (Fin.mk i hi)
      simp only at hv
      exact hv
    else
      simp only [not_lt] at hii
      have hieq : i + 1 = π.n := by apply Nat.le_antisymm <;> assumption
      rw [hieq]
      simp only [lt_self_iff_false, ↓reduceIte, tsub_self]
      rw [← hcont]
      have hv := π.valid (Fin.mk i hi)
      simp only at hv
      rw [← Nat.cast_add_one, hieq] at hv
      simp only [← Fin.natCast_eq_last]
      exact hv
  else
    simp only [hi, ↓reduceIte]
    simp only [not_lt] at hi
    apply Nat.lt_add_one_of_le at hi
    if hii : i + 1 < π.n then
      simp only at hii
      have hc := Nat.lt_trans hii hi
      simp only [lt_self_iff_false] at hc
    else
      simp only [hii, ↓reduceIte]
      have hv := π'.valid (i - π.n)
      rw [Nat.sub_add_comm (by
        rw [← Nat.lt_add_one_iff]
        exact hi)]
      exact hv⟩

/-
The *trace* of a path fragment is its projection onto 2^AP.
This makes traces sequences of sets of atomic propositions.
-/
abbrev InfiniteTrace := AbstractWorld
abbrev FiniteTrace := AbstractFiniteWorld

/--
A trace is either a finite trace or an infinite trace.
-/
inductive Trace (AP: Type) : Type
  | finite (trace : FiniteTrace AP)
  | infinite (trace : InfiniteTrace AP)

/--
Obtain the finite trace corresponding to a finite path fragment.
-/
def FiniteTraceFromFinitePathFragment {AP: Type} {TS : TransitionSystem AP} (π: FinitePathFragment TS) : FiniteTrace AP :=
  ⟨π.n, fun i ↦ TS.L (π.states i)⟩

/--
Obtain the infinite trace corresponding to an infinite path fragment.
-/
def InfiniteTraceFromInfinitePathFragment {AP: Type} {TS : TransitionSystem AP} (π: InfinitePathFragment TS) : InfiniteTrace AP :=
  fun i ↦ TS.L (π.states i)

/--
Obtain the trace corresponding to a path fragment.
-/
def TraceFromPathFragment {AP: Type} {TS : TransitionSystem AP} (π: PathFragment TS) : Trace AP :=
  match π with
  | PathFragment.finite π => Trace.finite (FiniteTraceFromFinitePathFragment π)
  | PathFragment.infinite π => Trace.infinite (InfiniteTraceFromInfinitePathFragment π)

/--
The set of traces corresponding to a set of path fragments.
-/
def TraceFromPathFragmentSet {AP: Type} {TS : TransitionSystem AP} (P : Set (PathFragment TS)) : Set (Trace AP) :=
  { trace | ∃ π ∈ P, trace = TraceFromPathFragment π }

/--
The set of traces of all paths starting from a given state.
-/
def TracesFromState {AP: Type} {TS : TransitionSystem AP} (s: TS.S) : Set (Trace AP) :=
  TraceFromPathFragmentSet (PathsFromState s)

/--
The set of finite traces of all finite paths starting from a given state.
-/
def TracesFinFromState {AP: Type} {TS : TransitionSystem AP} (s: TS.S) : Set (FiniteTrace AP) :=
  Set.image (fun π ↦ FiniteTraceFromFinitePathFragment π) (PathsFinFromState s)

/--
The set of all traces (finite or infinite) of the transition system.
-/
def Traces {AP: Type} (TS: TransitionSystem AP) : Set (Trace AP) :=
  ⋃ s ∈ {s | TS.I s}, TracesFromState s

/--
The set of all finite traces of the transition system.
-/
def TracesFin {AP: Type} (TS: TransitionSystem AP) : Set (FiniteTrace AP) :=
  { t | ∃ s ∈ {s | TS.I s}, t ∈ TracesFinFromState s }

/-
We will specifically be interested in Transition Systems with no terminal states. We will define some structures and functions to make it easier to work with them.
-/
structure TransitionSystemWithoutTerminalStates (AP: Type) where
  TS: TransitionSystem AP
  h: hasNoTerminalStates TS

abbrev TransitionSystemWTS := TransitionSystemWithoutTerminalStates

/--
Projections to fields of the underlying transition system.
-/
def TransitionSystemWTS.S {AP: Type} (TSwts: TransitionSystemWTS AP) := TSwts.TS.S
def TransitionSystemWTS.Act {AP: Type} (TSwts: TransitionSystemWTS AP) := TSwts.TS.Act
def TransitionSystemWTS.Trans {AP: Type} (TSwts: TransitionSystemWTS AP) := TSwts.TS.Trans
def TransitionSystemWTS.I {AP: Type} (TSwts: TransitionSystemWTS AP) := TSwts.TS.I
def TransitionSystemWTS.L {AP: Type} (TSwts: TransitionSystemWTS AP) := TSwts.TS.L

/--
Given a path fragment in a transition system without terminal states, obtain the corresponding infinite trace.
-/
def TraceFromPathWTS {AP: Type} {TSwts: TransitionSystemWTS AP} (π: PathFragment TSwts.TS) (h: π ∈ Paths TSwts.TS) : InfiniteTrace AP :=
  match π with
  | PathFragment.finite _ =>
      False.elim (by
        rw [Paths, Set.mem_setOf, isPath] at h
        obtain ⟨_, h₂⟩ := h
        rw [maximalIffInfinitePathFragment TSwts.h] at h₂
        unfold isInfinitePathFragment at h₂
        simp only at h₂)
  | PathFragment.infinite π' => InfiniteTraceFromInfinitePathFragment π'

/--
Given a path fragment from a state in a transition system without terminal states, obtain the corresponding infinite trace.
-/
def TraceFromPathFromStateWTS {AP: Type} {TSwts: TransitionSystemWTS AP} (s: TSwts.S) (π: PathFragment TSwts.TS) (h: π ∈ PathsFromState s) : InfiniteTrace AP :=
  match π with
  | PathFragment.finite _ => False.elim (by
      rw [PathsFromState, Set.mem_setOf] at h
      obtain ⟨h₁, _⟩ := h
      rw [maximalIffInfinitePathFragment TSwts.h] at h₁
      unfold isInfinitePathFragment at h₁
      simp only at h₁)
  | PathFragment.infinite π' => InfiniteTraceFromInfinitePathFragment π'

/--
Given a path fragment from an initial state in a transition system without terminal states, obtain the corresponding infinite trace.
-/
def TraceFromPathFromInitialStateWTS {AP: Type} {TSwts: TransitionSystemWTS AP} (s: TSwts.S) (π: PathFragment TSwts.TS) (h: π ∈ PathsFromState s) (h' : TSwts.I s) : InfiniteTrace AP :=
  TraceFromPathWTS π (by
    rw [Paths, Set.mem_setOf, isPath]
    rw [isInitialPathFragment]
    rw [PathsFromState, Set.mem_setOf] at h
    obtain ⟨hl, hr⟩ := h
    rw [hr]
    constructor <;> assumption)

/--
The set of infinite traces of all paths from a given state in a transition system without terminal states.
-/
def TracesFromStateWTS {AP: Type} {TSwts: TransitionSystemWTS AP} (s: TSwts.S) : Set (InfiniteTrace AP) :=
  { t | ∃ (p: PathFragment TSwts.TS) (h: p ∈ PathsFromState s), t = TraceFromPathFromStateWTS s p h }

/--
The set of infinite traces of all paths from an initial state in a transition system without terminal states.
-/
def TracesFromInitialStateWTS {AP: Type} {TSwts: TransitionSystemWTS AP} (s: TSwts.S) (h: TSwts.I s) : Set (InfiniteTrace AP) :=
  { t | ∃ (p: PathFragment TSwts.TS) (h': p ∈ PathsFromState s), t = TraceFromPathFromInitialStateWTS s p h' h }

/--
The set of all infinite traces of the transition system without terminal states.
-/
def TracesWTS {AP: Type} (TSwts: TransitionSystemWTS AP) : Set (InfiniteTrace AP) :=
  ⋃ s ∈ {s | TSwts.I s}, TracesFromInitialStateWTS s (by assumption)

/--
Given a path fragment in a transition system without terminal states, obtain the corresponding infinite path fragment.
-/
def PathToInfinitePathWTS {AP: Type} {TSwts: TransitionSystemWTS AP} (π: PathFragment TSwts.TS) (h: π ∈ Paths TSwts.TS) : InfinitePathFragment TSwts.TS :=
  match π with
  | PathFragment.finite _ =>
      False.elim (by
        rw [Paths, Set.mem_setOf, isPath] at h
        obtain ⟨_, h₂⟩ := h
        rw [maximalIffInfinitePathFragment TSwts.h] at h₂
        unfold isInfinitePathFragment at h₂
        simp only at h₂)
  | PathFragment.infinite π' => π'

/--
Given a path fragment from a state in a transition system without terminal states, obtain the corresponding infinite path fragment.
-/
def PathFromStateToInfinitePathWTS {AP: Type} {TSwts: TransitionSystemWTS AP} {s: TSwts.S} (π: PathFragment TSwts.TS) (h: π ∈ PathsFromState s) : InfinitePathFragment TSwts.TS :=
  match π with
  | PathFragment.finite _ => False.elim (by
      rw [PathsFromState, Set.mem_setOf] at h
      obtain ⟨h₁, _⟩ := h
      rw [maximalIffInfinitePathFragment TSwts.h] at h₁
      unfold isInfinitePathFragment at h₁
      simp only at h₁)
  | PathFragment.infinite π' => π'

end TransitionSystem
