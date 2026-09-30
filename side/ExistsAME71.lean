import FormalConjectures.OpenQuantumProblems.«35»

/-!
# `ExistsAME 7 1` holds under Formal Conjectures' definitions

Supports the review of FC#6497 (issue FC#6477). With local dimension `1` there is exactly one
configuration, so the state with amplitude `1` is normalized and every reduction is the `1 × 1`
identity, which is the maximally mixed state. Hence `ame_7_exists_iff` as currently stated
(for every `d : ℕ`) is false at `d = 1`, and the hypothesis `2 ≤ d` in FC#6497 is needed.
-/

open OpenQuantumProblem35

/-- The state with amplitude `1` on the single configuration of `Config 7 1`. -/
noncomputable def trivialState : StateVector 7 1 := mkStateVector fun _ => 1

theorem trivialState_isAME : IsAME trivialState := by
  refine ⟨?_, ?_⟩
  · rw [isNormalized_iff_norm_sq_eq_one, EuclideanSpace.norm_sq_eq]
    simp [trivialState]
  · intro π
    unfold HasMaximallyMixedFirstReduction
    ext x y
    obtain rfl : x = y := Subsingleton.elim x y
    simp [reducedDensityFirst, maximallyMixed, permuteState_apply, trivialState]

theorem existsAME_7_1 : ExistsAME 7 1 := ⟨trivialState, trivialState_isAME⟩

/-- The statement of `ame_7_exists_iff` before FC#6497 is refutable. -/
theorem ame_7_exists_iff_unrestricted_false : ¬ ∀ d : ℕ, (ExistsAME 7 d ↔ 3 ≤ d) := by
  intro h
  have := (h 1).1 existsAME_7_1
  omega

#print axioms existsAME_7_1
#print axioms ame_7_exists_iff_unrestricted_false
