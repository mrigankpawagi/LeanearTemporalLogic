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

### TransitionSystems

Defines transition systems and related concepts:

- `TransitionSystem` structure: `(S, Act, ⟶, I, L)` parameterized by atomic propositions
- Finite transition systems
- Successors and predecessors (direct and set-based)
- Terminal states
- Execution fragments (finite and infinite)
- Paths and path fragments
- Traces of executions and paths
- Specialized structures for transition systems without terminal states


### LTProperty

- Definition of Linear Time Properties as sets of infinite sequences

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
