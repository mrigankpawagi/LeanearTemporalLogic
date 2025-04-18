# LeanearTemporalLogic

This is a formalization of Linear Temporal Logic (LTL) in the Lean 4 theorem prover. The project implements the syntax and semantics of LTL, transition systems, and provides various lemmas and theorems about LTL and LT properties.

> [!NOTE]
> This project is a work in progress and may not be ready for use as a dependency. Contributions and feedback are welcome!

## Overview

[LTL](https://en.wikipedia.org/wiki/Linear_temporal_logic) is a logic for expressing constraints on *paths*. A *path* is a (countably infinite) sequence of *states*. A *state* is a set of propositional formulae (denoting the set of formulae that "hold in that state"). LTL provides operators for expressing constraints on states of a path, for instance, "formula $$X$$ holds in state $$S$$", "formula $$X$$ eventually holds after state $$S$$", "formula $$X$$ always holds after state $$S$$", etc. Paths can also be described as executions of a transition system. When dealing with paths with only finitely many propositional variables across all states (so that there are only finitely many inequivalent states, each of which can be thought of as a subset of the chosen set of propositional variables), LTL formulae can be equivalently described as automata (called [Büchi Automata](https://en.wikipedia.org/wiki/B%C3%BCchi_automaton)) which operate on infinite words (where the set of states is the alphabet).

LTL is of great interest for several software verification tasks, especially for concurrent programs, since the ability to check whether a path satisfies an LTL formula (what is called model-checking) immediately provides us the ability to check whether a program (real programs only have finitely many (program) states, but may run indefinitely and so may be modeled by paths over a finite set of states) violates a given specification expressed as an LTL formula (in which case we know that the program is buggy).

I am aware of at least four Lean 3 projects aiming to formalize LTL, and these are listed below. I would like to acknowledge any other projects that I may have missed. Since none of these are maintained or have been ported to Lean 4, the aim of *LeanearTemporalLogic* is to provide a Lean 4 formalization of LTL and several related tools and results.

1. [unitb/temporal-logic](https://github.com/unitb/temporal-logic)
2. [loganrjmurphy/lean-temporal](https://github.com/loganrjmurphy/lean-temporal)
3. [James-Oswald/linear-temporal-logic](https://github.com/James-Oswald/linear-temporal-logic)
4. [GaloisInc/lean-protocol-support/tree/master/galois/temporal](https://github.com/GaloisInc/lean-protocol-support/tree/master/galois/temporal)

I am using [Principles of Model Checking](https://web.eecs.umich.edu/~movaghar/Principles%20of%20Model%20Checking-Book-2008.pdf) by Baier and Katoen as my primary reference for this work.

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
  - `weakuntil` ($$\varphi \mathcal{W} \psi$$)

Propositional Logic (PL) formulas are defined as a subset of LTL formulas without temporal operators. This module provides appropriate syntactic or notational sugar to make it easier to write LTL formulas

This module also provides functions for calculating the length of formulae. While this was added merely as a sanity check for the syntax, it may be useful for reasoning about the time complexity of model-checking algorithms.

### AbstractWorlds

Provides definitions for `AbstractWorld` and `AbstractFiniteWorld` in order to create definitionally equivalent objects like traces and worlds.

### LTProperty

Provides a definition of Linear Time Properties as subsets of $$(2^{\text{AP}})^\omega$$ where $$\text{AP}$$ is the set of atomic propositions that parameterize LT Properties.

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

- `TransitionSystemWithoutTerminalStates` (abbreviated as `TransitionSystemWTS`): A transition system guaranteed to have no terminal states. The underlying `TransitionSystem` structure can be accessed like `TSwts.TS`, although all its fields can be directly accessed like `TSwts.S` or `TSwts.I`.
  - `TraceFromPathWTS`: Convert a (infinite) path fragment to a (infinte) trace
  - `TraceFromPathFromStateWTS`: Convert a (infinite) path fragment starting from a given state to a (infinite) trace
  - `TraceFromPathFromInitialStateWTS`: Convert a (infinite) path fragment starting from an initial state to a (infinite) trace
  - `TracesFromStateWTS`: Set of (infinite) traces of (infinite) paths starting from a given state
  - `TracesFromInitialStateWTS`: Set of (infinite) traces of (infinite) paths starting from an initial state
  - `TracesWTS`: Set of (infinite) traces of (infinite) paths starting from initial states
  - `PathToInfinitePathWTS`: Convert a PathFragment to an InfinitePathFragment
  - `PathFromStateToInfinitePathWTS`: Convert a PathFragment starting from a given state to an InfinitePathFragment

#### Theorems and Lemmas

- **Terminal States and Maximal Fragments**:
  - `maximalIffInfiniteExecutionFragment`: In transition systems without terminal states, an execution fragment is maximal if and only if it is infinite
  - `maximalIffInfinitePathFragment`: In transition systems without terminal states, a path fragment is maximal if and only if it is infinite

- **Path Properties**:
  - `path_starts_from_startState`: Every path is contained in the set of paths starting from its start state
  - `path_originates_from_state_if_noTerminalState`: In a transition system without terminal states, there is a path originating from every state

### Satisfaction

- **Core Type Classes**:
  - `Satisfaction`: Generic type class for defining satisfaction relations
  - `Equivalent`: Type class for defining equivalence relations

- **Worlds**:
  - `World`: Represents a sequence of states where each state is a set of atomic propositions
  - `FiniteWorld`: Represents a world with a finite number of states
  - `Suffix`: Function to create a suffix of a world starting at a specific index
  - `Prefix`: Function to create a prefix (initial segment) of a world
  - `PrefixOfPrefix`: Function to create a prefix of a prefix
  - `pref`: Function that returns the set of all prefixes of a world
  - `prefLTProperty`: Set of all prefixes of traces in an LT property
  - `closureLTProperty`: Closure of an LT property
  - **Some useful lemmas**
    - `Suffix.composition`: $\sigma[i\ldots][j\ldots] = \sigma[i+j\ldots]$
    - `Suffix.zero_identity`: $\sigma[0\ldots] = \sigma$
    - `prefix_monotonicity`: Prefixes of a set contains the prefixes of its subsets
    - `closure_monotonicity`: Closure of a set contains the closure of its subsets
    - `finite_traces_are_prefixes`: Finite traces of a system are prefixes of its infinite traces
    - `closure_contains_property`: A property is contained in its closure
    - `prefix_of_closure_is_prefix`: Prefixes of a closure coincide with the prefixes of the original property
    - `prefix_distributes_over_union`: Prefixes of a union of two sets coincide with the union of the prefixes of the sets
    - `closure_distributes_over_union`: Closure of a union of two sets coincides with the union of the closures of the sets
    - `closure_idempotent`: Closure of a closure is the closure itself

- **Satisfaction of LTL Formulae by Worlds**:
  - $$\sigma \vDash \varphi$$: A world $$\sigma$$ satisfies an LTL formula $$\varphi$$
  - $$s \vDash \varphi$$: A state $$s$$ satisfies an LTL formula $$\varphi$$
  - **Derived rules for satisfaction**
    - `world_satisfies_negation`: $$(σ ⊨ (¬ ϕ)) ↔ (¬ (σ ⊨ ϕ))$$
      - `world_satisfies_or`: $$(σ ⊨ (ϕ₁ ∨ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∨ (σ ⊨ ϕ₂))$$
    - `world_satisfies_and`: $$(σ ⊨ (ϕ₁ ∧ ϕ₂)) ↔ ((σ ⊨ ϕ₁) ∧ (σ ⊨ ϕ₂))$$
    - `world_satisfies_next`: $$(σ ⊨ (◯ ϕ)) ↔ ((σ[1…]) ⊨ ϕ)$$
    - `world_satisfies_until`: $$(σ ⊨ (ϕ₁ 𝓤 ϕ₂)) ↔ ∃ j, (((σ[j…]) ⊨ ϕ₂) ∧ ∀ (k: ℕ), (k < j → ((σ[k…]) ⊨ ϕ₁)))$$
    - `world_satisfies_eventually`: $$(σ ⊨ (♢ ϕ)) ↔ ∃ i, ((σ[i…]) ⊨ ϕ)$$
    - `world_satisfies_always`: $$(σ ⊨ (□ ϕ)) ↔ ∀ i, ((σ[i…]) ⊨ ϕ)$$
    - `world_satisfies_always_eventually`: $$(σ ⊨ (□ ♢ ϕ)) ↔ ∀ i, ∃ j, ((σ[i+j…]) ⊨ ϕ)$$
    - `world_satisfies_eventually_always`: $$(σ ⊨ (♢ □ ϕ)) ↔ ∃ i, ∀ j, ((σ[i+j…]) ⊨ ϕ)$$
    - `world_satisfies_weakuntil`: $$(σ ⊨ (ϕ₁ 𝓦 ϕ₂)) ↔ ((σ ⊨ (ϕ₁ 𝓤 ϕ₂)) ∨ (σ ⊨ (□ ϕ₁)))$$
    - `satisfies_for_first_time_iff_satisfies`: If a world satisfies an LTL formula, it satisfies it for the first time at some index
  - `Worlds`: Maps an LTL formula to the set of worlds that satisfy it

- **Equivalence of LTL Formulae**:
  - $$ϕ ≡ ψ$$: Two LTL formulae $$ϕ$$ and $$ψ$$ are equivalent if they are satisfied by the same set of worlds
  - `equivalent_ltl_refl`, `equivalent_ltl_symm`, `equivalent_ltl_trans`: Formula equivalence is an equivalence relation
  - **Derived rules for equivalence**
    - `equivalent_ltl_preserves_negation`: $$(ϕ ≡ ψ) ↔ ((¬ ϕ) ≡ (¬ ψ))$$
    - `equivalent_ltl_preserves_always`: $$(ϕ ≡ ψ) ↔ ((□ ϕ) ≡ (□ ψ))$$
    - `ltl_double_negation`: $$(¬ (¬ ϕ)) ≡ ϕ$$
    - **Dualities**
      - `ltl_duality_next`: $$(¬ (◯ ϕ)) ≡ (◯ (¬ ϕ))$$
      - `ltl_duality_eventually`: $$(¬ (♢ ϕ)) ≡ (□ (¬ ϕ))$$
      - `ltl_duality_always`: $$(¬ (□ ϕ)) ≡ (♢ (¬ ϕ))$$
      - `ltl_duality_until` : $$(¬ (ϕ 𝓤 ψ)) ≡ ((ϕ ∧ (¬ ψ)) 𝓦 ((¬ ϕ) ∧ (¬ ψ)))$$
      - `ltl_duality_weakuntil`: $$(¬ (ϕ 𝓦 ψ)) ≡ ((ϕ ∧ (¬ ψ)) 𝓤 ((¬ ϕ) ∧ (¬ ψ)))$$
    - **Idempotence**
      - `ltl_idempotence_eventually`: $$(♢ (♢ ϕ)) ≡ (♢ ϕ)$$
      - `ltl_idempotence_always`: $$(□ (□ ϕ)) ≡ (□ ϕ)$$
      - `ltl_idempotence_until_left`: $$((ϕ 𝓤 ϕ) 𝓤 ψ) ≡ (ϕ 𝓤 ψ)$$
      - `ltl_idempotence_until_right`: $$ϕ 𝓤 (ψ 𝓤 ψ) ≡ ϕ 𝓤 ψ$$
    - **Absorption**
      - `ltl_absorption_always_eventually`: $$(♢ (□ (♢ ϕ))) ≡ (□ (♢ ϕ))$$
      - `ltl_absorption_eventually_always`: $$(□ (♢ (□ ϕ))) ≡ (♢ (□ ϕ))$$
    - **Expansions**
      - `ltl_expansion_until`: $$(ϕ 𝓤 ψ) ≡ (ψ ∨ (ϕ ∧ (◯ (ϕ 𝓤 ψ))))$$
      - `ltl_expansion_weakuntil`: $$(ϕ 𝓦 ψ) ≡ (ψ ∨ (ϕ ∧ (◯ (ϕ 𝓦 ψ))))$$
      - `ltl_expansion_eventually`: $$(♢ ϕ) ≡ (ϕ ∨ (◯ (♢ ϕ)))$$
      - `ltl_expansion_always`: $$(□ ϕ) ≡ (ϕ ∧ (◯ (□ ϕ)))$$
    - **Distributivity**
      - `ltl_distributive_next_until`: $$(◯ (ϕ 𝓤 ψ)) ≡ ((◯ ϕ) 𝓤 (◯ ψ))$$
      - `ltl_distributive_eventually_or`: $$(♢ (ϕ ∨ ψ)) ≡ ((♢ ϕ) ∨ (♢ ψ))$$
      - `ltl_distributive_always_and`: $$(□ (ϕ ∧ ψ)) ≡ ((□ ϕ) ∧ (□ ψ))$$
  - `until_least_solution_of_expansion_law`: Until is the Least Solution of the Expansion Law
  - `weakuntil_greatest_solution_of_expansion_law`: Weak Until is the Greatest Solution of the Expansion Law
  
- **Satisfaction of PL Formulae by Sets of Atomic Propositions**:
  - $$A \vDash \varphi$$: A set of atomic propositions $$A$$ satisfies a PL formula $$\varphi$$
  - **Derived rules for satisfaction**
    - `set_satisfies_negation`: $$(A ⊨ (¬ ϕ)) ↔ (¬ (A ⊨ ϕ))$$
    - `set_satisfies_or`: $$(A ⊨ (ϕ₁ ∨ ϕ₂)) ↔ ((A ⊨ ϕ₁) ∨ (A ⊨ ϕ₂))$$
    - `set_satisfies_and`: $$(A ⊨ (ϕ₁ ∧ ϕ₂)) ↔ ((A ⊨ ϕ₁) ∧ (A ⊨ ϕ₂))$$

- **Satisfaction of LT Properties by Transition Systems**:
  - $$TS \vDash P$$: A transition system satisfies an LT property
  - $$TSwts \vDash P$$: A transition system without terminal states satisfies an LT property
  - **Auxiliary Lemmas and Theorems**
    - `ltproperty_satisfaction_allPaths`: A transition system satisfies a property if the traces of all its paths are in the property
    - `trace_inclusion_and_LTProperties`: Trace Inclusion and LT Properties
    - `trace_equivalence_and_LTProperties`: Trace Equivalence and LT Properties
    - `finite_trace_and_trace_inclusion`: (WIP) Finite Trace and Trace Inclusion
  - **Results for special kinds of LT properties**
    - **Invariants**
      - `invariant_satisfaction_reachability`: A system satisfies an invariant property iff all reachable states satisfy the invariant condition
    - **Safety Properties**
      - **Additional Structures and Lemmas**
        - `BadPref`, `MinBadPref`: Sets of all bad prefixes and minimal bad prefixes for a property
        - `safety_closure`: A property is a safety property iff it equals its closure
        - `closure_of_traces`: The closure of a system's traces is a safety property that the system satisfies
      - `safety_satisfaction`: A system satisfies a safety property if no bad prefix of the property is a finite trace of the system
      - `safety_finite_trace_inclusion`: Finite Trace Inclusion and Safety Properties
      - `safety_finite_trace_equivalence`: Finite Trace Equivalence and Safety Properties
    - **Liveness Properties**
      - `intersection_safety_liveness`: The only LT property that is both a safety and a liveness property is the trivial property
      - `decomposition`: Any LT property can be decomposed into an intersection of a safety property and a liveness property
      - `sharpest_decomposition`: The decomposition of a property into an intersection of its closure and its union with the complement of its closure is the sharpest decomposition into a safety and a liveness property

## Future Work

### Planned goals

- Proving a theorem about Relating Finite Trace and Trace Inclusion (WIP)
- Formalizing fairness and related results
- Formalizing results about Positive Normal Form

### Ambitious goals

- Implementing (checked) algorithms for model-checking LT properties, with particular algorithms for invariant, safety, and liveness properties
- Implementing an (checked) algorithm for model-checking LTL Formulae
- Formalizing Büchi automata and proving regularity results

### Quality goals

- Replace `simp` tactics with `simp only` except when closing the goal
- Replace structures with special properties by inherited structures (e.g., `TransitionSystemWTS`)
- Create type classes for overloaded operations like `Post`, `Pre`, `pref`, etc.
