/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import FormalConjectures.OpenQuantumProblems.«35»

/-!
# The sign pattern of the five-qubit ring state

The ring graph state on five qubits has amplitude proportional to
`(-1) ^ (x₀x₁ + x₁x₂ + x₂x₃ + x₃x₄ + x₄x₀)`. This file proves the one finite fact the AME
proof needs: after any permutation of the parties, summing the product of two signs over the
three traced parties gives `8` when the two kept configurations agree and `0` otherwise.
-/

namespace AME52

open OpenQuantumProblem35

/-- The number of edges of the pentagon with both ends set to `1` in `x`. -/
def ringParity (x : Config 5 2) : ℕ :=
  ∑ i : Fin 5, (x i).val * (x (i + 1)).val

/-- The sign `(-1) ^ (x₀x₁ + x₁x₂ + x₂x₃ + x₃x₄ + x₄x₀)` of the ring state at `x`. -/
def ringSign (x : Config 5 2) : ℤ :=
  (-1) ^ ringParity x

/-- The finite core: for every permutation, the traced sum of sign products is `8` on the
diagonal and `0` off it. Checked by the kernel over all 120 permutations. Stated with `5 / 2`
and `5 - 5 / 2`, as in Formal Conjectures' `IsAME`, so that it rewrites directly inside
`HasMaximallyMixedFirstReduction`. -/
theorem ringSign_trace (π : Equiv.Perm (Fin 5)) (x y : Config (5 / 2) 2) :
    ∑ z : Config (5 - 5 / 2) 2,
        ringSign (permuteConfig π (combineFirst (n := 5) (d := 2) (5 / 2)
          (Nat.div_le_self 5 2) x z)) *
        ringSign (permuteConfig π (combineFirst (n := 5) (d := 2) (5 / 2)
          (Nat.div_le_self 5 2) y z)) =
      if x = y then 8 else 0 := by
  revert π x y
  decide +kernel

end AME52
