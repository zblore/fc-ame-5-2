/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME52.Existence

/-!
# The Formal Conjectures target

`OpenQuantumProblem35.ame_5_2_exists` in Formal Conjectures states `ExistsAME 5 2` and leaves
it as `sorry`. This file proves the same proposition from the pinned Formal Conjectures
definitions, without using that declaration.
-/

namespace AME52

open OpenQuantumProblem35

/-- The ring state is absolutely maximally entangled. -/
theorem ringState_isAME : IsAME ringState :=
  ⟨ringState_isNormalized, ringState_reduction⟩

/-- An AME(5,2) state exists. -/
theorem ame_5_2_exists : ExistsAME 5 2 :=
  ⟨ringState, ringState_isAME⟩

end AME52
