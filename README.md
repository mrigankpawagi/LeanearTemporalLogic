# LeanearTemporalLogic

This is a formalization of Linear Temporal Logic (LTL) in the Lean 4 theorem prover. The project implements the syntax and semantics of LTL, transition systems, and provides various lemmae and theorems about LTL and LT properties.

> [!NOTE]
> This project is a work in progress and may not be ready for use as a dependency. Contributions and feedback are welcome!

## Overview

[LTL](https://en.wikipedia.org/wiki/Linear_temporal_logic) is a logic for expressing constraints on *paths*. A *path* is a (countably infinite) sequence of *states*. A *state* is a set of propositional formulae (denoting the set of formulae that "hold in that state"). LTL provides operators for expressing constraints on states of a path, for instance, "formula $$X$$ holds in state $$S$$", "formula $$X$$ eventually holds after state $$S$$", "formula $$X$$ always holds after state $$S$$", etc. Paths can also be described as executions of a transition system. When dealing with paths with only finitely many propositional variables across all states (so that there are only finitely many inequivalent states, each of which can be thought of as a subset of the chosen set of propositional variables), LTL formulae can be equivalently described as automata (called [Büchi Automata](https://en.wikipedia.org/wiki/B%C3%BCchi_automaton)) which operate on infinite words (where the set of states is the alphabet).

LTL is of great interest for several software verification tasks, especially for concurrent programs, since the ability to check whether a path satisfies an LTL formula (what is called model-checking) immediately provides us the ability to check whether a program (real programs only have finitely many (program) states, but may run indefinitely and so may be modelled by paths over a finite set of states) violates a given specification expressed as an LTL formula (in which case we know that the program is buggy).

I am aware of at least four Lean 3 projects aiming to formalize LTL, and these are listed below. I would like to acknowledge any other projects that I may have missed. Since none of these are maintained or have been ported to Lean 4, the aim of *LeanearTemporalLogic* is to provide a Lean 4 formalization of LTL and several related tools and results.

1. [unitb/temporal-logic](https://github.com/unitb/temporal-logic)
2. [loganrjmurphy/lean-temporal](https://github.com/loganrjmurphy/lean-temporal)
3. [James-Oswald/linear-temporal-logic](https://github.com/James-Oswald/linear-temporal-logic)
4. [GaloisInc/lean-protocol-support/tree/master/galois/temporal](https://github.com/GaloisInc/lean-protocol-support/tree/master/galois/temporal)

## Project Structure

The project is organized into the following modules.

### LTL

Implements the syntax of Linear Temporal Logic with basic and derived operators. Note that LTL formulae are parameterized by the set of atomic propositions.

- Basic operators:
  - `True` ($$\top$$)
  - `atom a` (atomic proposition)
  - `not φ` ($$\neg\varphi$$)
  - `and φ ψ` ($$\varphi \land \psi$$)
  - `next φ` ($$\bigcirc\varphi$$)
  - `until φ ψ` ($$\varphi \mathcal{U} \psi$$)

- Derived operators:
  - `or φ ψ` ($$\varphi \lor \psi$$)
  - `eventually φ` ($$\diamondsuit\varphi$$)
  - `always φ` ($$\square\varphi$$)
  - `False` ($$\bot$$)

Propositional Logic (PL) formulas are defined as a subset of LTL formulas without temporal operators. This module provides appropriate syntactic or notational sugar to make it easier to write LTL formulas

This module also provides functions for calculating the length of formulae. While this was added merely as a sanity check for the syntax, it may be useful for reasoning about the time complexity of model-checking algorithms.

### LTProperty

Provides a definition of Linear Time Properties as subsets of $$(2^{\text{AP}})^\omega$$ where $$\text{AP}$$ is the set of atomic propositions that parameterizes LT Properties.

### TransitionSystems

Implements transition systems and related concepts for modeling state-based systems:

- `TransitionSystem`: Core structure parameterized by atomic propositions, consisting of:
  - `S`: Set of states
  - `Act`: Set of actions/transitions
  - `Trans`: Transition relation between states via actions
  - `I`: Set of initial states
  - `L`: Labeling function mapping states to sets of atomic propositions

- **System Properties**:
  - `isFinite`: Determines if a transition system has finite states, actions, and atomic propositions
  - `hasNoTerminalStates`: Specifies that a transition system contains no terminal states
  - `isTerminalState`: Identifies states without successors

- **State Relations and Successors**:
  - `PostAction`: Set of successors of a state via a specific action
  - `Post`: Set of all successors of a state (via any action)
  - `PreAction`: Set of predecessors of a state via a specific action
  - `Pre`: Set of all predecessors of a state (via any action)
  - `PostActionSet`, `PostSet`, `PreActionSet`, `PreSet`: Extended versions for sets of states

- **Execution Fragments**:
  - `FiniteExecutionFragment`: Finite alternating sequence of states and actions with valid transitions
  - `InfiniteExecutionFragment`: Infinite alternating sequence of states and actions with valid transitions
  - `ExecutionFragment`: Either a finite or infinite execution fragment
  - `startStateExecutionFragment`, `endStateExecutionFragment`: Extract the start and end states (`Option.none` for infinite fragments) of an execution respectively
  - `isFiniteExecutionFragment`, `isInfiniteExecutionFragment`: Determines if an execution fragment is finite or infinite
  - `isMaximalExecutionFragment`: Determines if an execution fragment is maximal, i.e., either finite and ending in a terminal state, or infinite
  - `isInitialExecutionFragment`: Determines if an execution fragment starts from an initial state
  - `isExecution`: Defines an execution as an initial, maximal execution fragment

- **Path Fragments**
  - `FinitePathFragment`: Finite sequence of states with valid transitions
  - `InfinitePathFragment`: Infinite sequence of states with valid transitions
  - `PathFragment`: Either a finite or infinite path fragment
  - `getPathState`: Extracts the state at a given index in a path fragment
  - `startStatePathFragment`, `endStatePathFragment`: Extract the start and end states (`Option.none` for infinite fragments)
   of a path fragment
  - `lengthPathFragment`: Returns the length of a path fragment (`Option.none` for infinite fragments)
  - `isFinitePathFragment`, `isInfinitePathFragment`: Determines if a path fragment is finite or infinite
  - `isMaximalPathFragment`: Determines if a path fragment is maximal, i.e., either finite and ending in a terminal state, or infinite
  - `isInitialPathFragment`: Determines if a path fragment starts from an initial state
  - `PathFragment.concatenate_finite_and_infinite`: Concatenates a finite and infinite path fragment

- **Conversion between Execution Fragments and Path Fragments**:
  - `finiteExecutionFragmentToFinitePathFragment`, `infiniteExecutionFragmentToInfinitePathFragment`: Convert finite and infinite execution fragments to finite and infinite path fragments respectively
  - `executionFragmentToPathFragment`: Convert an execution fragment to a path fragment (combining the above functions)
  - (noncomputable) `finitePathFragmentToFiniteExecutionFragment`, `infinitePathFragmentToInfiniteExecutionFragment`: Convert finite and infinite path fragments to finite and infinite
  - (noncomputable) `pathFragmentToExecutionFragment`: Convert a path fragment to an execution fragment (combining the above functions)

- **Paths and Reachability**:
  - `isReachableState`: Determines if a state is reachable through an initial, finite execution fragment
  - `Reach`: Set of all reachable states in a transition system
  - `isPath`: Defines a path as an initial, maximal path fragment
  - `Paths`: Set of all paths in a transition system
  - `PathsFromState`: Set of all paths starting from a given state
  - `PathsFin`: Set of all finite paths in a transition system
  - `PathsFinFromState`: Set of all finite paths starting from a given state

- **Traces**:
  - `FiniteTrace`: Finite sequence of sets of atomic propositions
  - `InfiniteTrace`: Infinite sequence of sets of atomic propositions
  - `Trace`: Either a finite or infinite trace
  - `FiniteTraceFromFinitePathFragment`, `InfiniteTraceFromInfinitePathFragment`: Convert finite and infinite path fragments to finite and infinite traces respectively
  - `TraceFromPathFragment`: Convert a path fragment to a trace (combining the above functions)
  - `TraceFromPathFragmentSet`: Convert a set of path fragments to a set of traces
  - `TracesFromState`: Set of traces of paths starting from a given state
  - `TracesFinFromState`: Set of (finite) traces of finite paths starting from a given state
  - `Traces`: Sets of all traces starting from initial states
  - `TracesFin`: Sets of all finite traces starting from initial states

- `TransitionSystemWithoutTerminalStates` (abbreviated as `TransitionSystemWTS`): A transition system guaranteed to have no terminal states
  - `TraceFromPathWTS`: Convert a (infinite) path fragment to a (infinte) trace
  - `TraceFromPathFromStateWTS`: Convert a (infinite) path fragment starting from a given state to a (infinite) trace
  - `TraceFromPathFromInitialStateWTS`: Convert a (infinite) path fragment starting from an initial state to a (infinite) trace
  - `TracesFromStateWTS`: Set of (infinite) traces of (infinite) paths starting from a given state
  - `TracesFromInitialStateWTS`: Set of (infinite) traces of (infinite) paths starting from an initial state
  - `TracesWTS`: Set of (infinite) traces of (infinite) paths starting from initial states

#### Theorems and Lemmas

- **Terminal States and Maximal Fragments**:
  - `maximalIffInfiniteExecutionFragment`: In transition systems without terminal states, an execution fragment is maximal if and only if it is infinite
  - `maximalIffInfinitePathFragment`: In transition systems without terminal states, a path fragment is maximal if and only if it is infinite

- **Path Properties**:
  - `path_starts_from_startState`: Every path is contained in the set of paths starting from its start state
  - `path_originates_from_state_if_noTerminalState`: In a transition system without terminal states, there is a path originating from every state

### Satisfaction

Implements the semantics of LTL and provides various proofs:

- World-based semantics for LTL formulas
- Satisfaction relations between worlds and formulas
- Suffix operations on worlds
- Equivalence relation between LTL formulas
- Key theorems and equivalences:
  - Double negation
  - Dualities for temporal operators
  - Idempotence of temporal operators
  - Absorption laws
  - Expansion laws for until, eventually, and always
  - Distributive properties
  - "Until is the Least Solution of the Expansion Law" theorem
- Satisfaction of LT properties by transition systems
- Trace inclusion and equivalence theorems
- Invariant properties and their relationship to reachability

## Key Formalizations and Theorems

The project includes formalizations and proofs of many important LTL concepts:

1. **LTL Equivalences**:
   - `ltl_double_negation`: ¬¬φ ≡ φ
   - `ltl_duality_next`: ¬◯φ ≡ ◯¬φ
   - `ltl_duality_eventually`: ¬♢φ ≡ □¬φ
   - `ltl_duality_always`: ¬□φ ≡ ♢¬φ
   - `ltl_idempotence_eventually`: ♢♢φ ≡ ♢φ
   - `ltl_idempotence_always`: □□φ ≡ □φ
   - `ltl_absorption_always_eventually`: ♢□♢φ ≡ □♢φ
   - `ltl_absorption_eventually_always`: □♢□φ ≡ ♢□φ
   - `ltl_expansion_until`: φ 𝓤 ψ ≡ ψ ∨ (φ ∧ ◯(φ 𝓤 ψ))
   - `ltl_expansion_eventually`: ♢φ ≡ φ ∨ ◯♢φ
   - `ltl_expansion_always`: □φ ≡ φ ∧ ◯□φ

2. **Semantic Properties**:
   - `until_least_solution_of_expansion_law`: Proof that Until is the least solution of its expansion law
   - `world_satisfies_eventually_always`: Characterization of ♢□φ
   - `world_satisfies_always_eventually`: Characterization of □♢φ

3. **System Verification**:
   - `trace_inclusion_and_LTProperties`: Relation between trace inclusion and LT properties
   - `trace_equivalence_and_LTProperties`: Trace equivalence theorem
   - `invariant_satisfaction_reachability`: Characterization of invariant verification through reachability analysis

## Future Work

Potential future extensions to this formalization include:

- Adding more complex temporal operators (e.g., release, weak until)
- Implementing model checking algorithms for LTL
- Defining fairness and other characteristics for LT properties
- Proving results about Büchi automata
