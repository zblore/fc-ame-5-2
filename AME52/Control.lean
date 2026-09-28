/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME52.Sign

/-!
# Control: the check is not vacuous

Dropping one edge of the pentagon gives the five-qubit path state, which is not AME. The same
kernel check rejects it, so `ringSign_trace` does not hold for a trivial reason.
-/

namespace AME52

open OpenQuantumProblem35

/-- The sign of the five-qubit path state: the ring without the edge `x₄x₀`. -/
def pathSign (x : Config 5 2) : ℤ :=
  (-1) ^ ∑ i : Fin 4, (x i.castSucc).val * (x i.succ).val

/-- The path state fails the identity that `ringSign_trace` proves for the ring. The diagonal
cannot fail for any sign pattern, so the failure is off the diagonal. -/
theorem pathSign_trace_fails :
    ¬ ∀ (π : Equiv.Perm (Fin 5)) (x y : Config (5 / 2) 2),
      ∑ z : Config (5 - 5 / 2) 2,
          pathSign (permuteConfig π (combineFirst (n := 5) (d := 2) (5 / 2)
            (Nat.div_le_self 5 2) x z)) *
          pathSign (permuteConfig π (combineFirst (n := 5) (d := 2) (5 / 2)
            (Nat.div_le_self 5 2) y z)) =
        if x = y then 8 else 0 := by
  decide +kernel

/-- The failure made explicit. With the parties in order, the kept configurations `00` and
`10` give `8` where the ring gives `0`: flipping party `0` changes no path edge, because the
path has no edge `x₄x₀`. -/
example :
    ∑ z : Config (5 - 5 / 2) 2,
        pathSign (permuteConfig 1 (combineFirst (n := 5) (d := 2) (5 / 2)
          (Nat.div_le_self 5 2) ![0, 0] z)) *
        pathSign (permuteConfig 1 (combineFirst (n := 5) (d := 2) (5 / 2)
          (Nat.div_le_self 5 2) ![1, 0] z)) = 8 := by
  decide +kernel

end AME52
