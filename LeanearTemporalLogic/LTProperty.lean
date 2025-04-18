import Mathlib
import LeanearTemporalLogic.AbstractWorlds

/-!
We define **Linear Time Properties**, or LT properties, over a set of atomic propositions.
-/
def LTProperty (AP: Type) := Set (AbstractWorld AP)
