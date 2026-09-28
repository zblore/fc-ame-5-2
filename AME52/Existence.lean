/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME52.State

/-!
# Every two-party reduction of the ring state is maximally mixed

An entry of the reduction is `1/32` times the traced sum of sign products, and
`ringSign_trace` says that sum is `8` on the diagonal and `0` off it. So every entry is
`1/4` or `0`, which is the maximally mixed state on two qubits.
-/

namespace AME52

open OpenQuantumProblem35

/-- `uniformCoeff 32` times its conjugate is `1/32`. -/
lemma uniformCoeff_32_mul_star : uniformCoeff 32 * star (uniformCoeff 32) = (32 : ℂ)⁻¹ := by
  simpa using uniformCoeff_mul_star 32

/-- One term of the reduction: the product of two amplitudes is `1/32` times the product of
their signs. -/
lemma amplitude_mul_star (a b : ℤ) :
    uniformCoeff 32 * (a : ℂ) * star (uniformCoeff 32 * (b : ℂ)) =
      (32 : ℂ)⁻¹ * ((a * b : ℤ) : ℂ) := by
  rw [← uniformCoeff_32_mul_star, star_mul', star_intCast]
  push_cast
  ring

/-- After any permutation of the parties, the ring state has a maximally mixed reduction on
the first two parties. -/
theorem ringState_reduction (π : Equiv.Perm (Fin 5)) :
    HasMaximallyMixedFirstReduction (n := 5) (d := 2) (5 / 2) (Nat.div_le_self 5 2)
      (permuteState π ringState) := by
  unfold HasMaximallyMixedFirstReduction
  ext x y
  rw [maximallyMixed_apply]
  unfold reducedDensityFirst
  simp only [permuteState_apply, ringState_apply, amplitude_mul_star]
  rw [← Finset.mul_sum, ← Int.cast_sum, ringSign_trace]
  split_ifs <;> norm_num [card_config]

end AME52
