/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME52.Sign

/-!
# The five-qubit ring state

Every amplitude is `±1/√32`, with the sign given by `ringSign`.
-/

namespace AME52

open OpenQuantumProblem35

/-- The five-qubit ring graph state. -/
noncomputable def ringState : StateVector 5 2 :=
  mkStateVector fun x ↦ uniformCoeff 32 * (ringSign x : ℂ)

@[simp]
lemma ringState_apply (x : Config 5 2) :
    ringState x = uniformCoeff 32 * (ringSign x : ℂ) := rfl

/-- Every sign has norm one. -/
lemma norm_ringSign (x : Config 5 2) : ‖(ringSign x : ℂ)‖ = 1 := by
  simp [ringSign]

/-- The ring state is normalized: 32 amplitudes, each of squared norm `1/32`. -/
lemma ringState_isNormalized : IsNormalized ringState := by
  rw [isNormalized_iff_norm_sq_eq_one]
  calc ‖ringState‖ ^ 2 = ∑ x : Config 5 2, ‖ringState x‖ ^ 2 := by
        simpa using EuclideanSpace.norm_sq_eq ringState
    _ = ∑ _x : Config 5 2, ‖uniformCoeff 32‖ ^ 2 := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [ringState_apply, norm_mul, norm_ringSign, mul_one]
    _ = 1 := by
        simp [Finset.sum_const, uniformCoeff_norm_sq]

end AME52
