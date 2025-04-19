/-
# LTProperty

This module defines Linear Time Properties (LT properties) over a set of atomic propositions.
An LT property is a set of worlds, i.e., infinite sequences of sets of atomic propositions,
representing the behaviors or executions that satisfy a given specification.
-/

import Mathlib
import LeanearTemporalLogic.AbstractWorlds

/--
An `LTProperty AP` is an LT property with atomic propositions of type `AP`.
These properties can be used to specify the specification or desired behavior of a system, for example,
through a set of all allowed sequences of states, where states are sets of atomic propositions that can
be thought to be true in that state.
-/
def LTProperty (AP: Type) := Set (AbstractWorld AP)
