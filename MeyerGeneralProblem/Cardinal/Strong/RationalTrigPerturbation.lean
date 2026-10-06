module

public import MeyerGeneralProblem.Cardinal.Strong.RationalTrigPrecision
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! Safe executable rational clamping and actual real-input trigonometric errors. -/

namespace MeyerGeneralProblem.StrongParity

/-- Executable rational projection onto the actual trigonometric value interval. -/
def rationalUnitClamp (q : ℚ) : ℚ := max (-1) (min 1 q)

/-- The bounded executable sine value used in safe phase composition. -/
def rationalBoundedSinApprox (q : ℚ) (p : ℕ) : ℚ := rationalUnitClamp (rationalSinApprox q p)

/-- The bounded executable cosine value used in safe phase composition. -/
def rationalBoundedCosApprox (q : ℚ) (p : ℕ) : ℚ := rationalUnitClamp (rationalCosApprox q p)

noncomputable section

theorem rationalUnitClamp_bounds (q : ℚ) : -1 ≤ rationalUnitClamp q ∧ rationalUnitClamp q ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Rational clamping cannot increase error against an ACTUAL value in the interval. -/
theorem rationalUnitClamp_error (q : ℚ) {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) :
    |(rationalUnitClamp q : ℝ) - x| ≤ |(q : ℝ) - x| := by
  have hc : (rationalUnitClamp q : ℝ) = max (-1) (min 1 (q : ℝ)) := by
    simp [rationalUnitClamp]
  rw [hc]
  by_cases hi : 1 ≤ (q : ℝ)
  · rw [min_eq_left hi, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [abs_of_nonneg (by linarith [hx.2]), abs_of_nonneg (by linarith [hx.2])]
    linarith
  by_cases lo : (q : ℝ) ≤ -1
  · rw [min_eq_right (by linarith : (q : ℝ) ≤ 1), max_eq_left lo]
    rw [abs_of_nonpos (by linarith [hx.1]), abs_of_nonpos (by linarith [hx.1])]
    linarith
  rw [min_eq_right (le_of_not_ge hi), max_eq_right (le_of_not_ge lo)]

theorem rationalBoundedSinApprox_error (q : ℚ) (p : ℕ) :
    |(rationalBoundedSinApprox q p : ℝ) - Real.sin (q : ℝ)| ≤ 1 / (2 : ℝ) ^ p :=
  (rationalUnitClamp_error _ ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩).trans
    (rationalSinApprox_error q p)

theorem rationalBoundedCosApprox_error (q : ℚ) (p : ℕ) :
    |(rationalBoundedCosApprox q p : ℝ) - Real.cos (q : ℝ)| ≤ 1 / (2 : ℝ) ^ p :=
  (rationalUnitClamp_error _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩).trans
    (rationalCosApprox_error q p)

/-- Actual error after combining the computed sine value with an explicit input error. -/
theorem rationalBoundedSinApprox_real_input_error (q : ℚ) (p : ℕ) {x epsilon : ℝ}
    (hq : |(q : ℝ) - x| ≤ epsilon) :
    |(rationalBoundedSinApprox q p : ℝ) - Real.sin x| ≤ 1 / (2 : ℝ) ^ p + epsilon := by
  calc
    _ ≤ |(rationalBoundedSinApprox q p : ℝ) - Real.sin (q : ℝ)| +
        |Real.sin (q : ℝ) - Real.sin x| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (rationalBoundedSinApprox_error q p)
      ((Real.abs_sin_sub_sin_le _ _).trans hq)

/-- Actual error after combining the computed cosine value with an explicit input error. -/
theorem rationalBoundedCosApprox_real_input_error (q : ℚ) (p : ℕ) {x epsilon : ℝ}
    (hq : |(q : ℝ) - x| ≤ epsilon) :
    |(rationalBoundedCosApprox q p : ℝ) - Real.cos x| ≤ 1 / (2 : ℝ) ^ p + epsilon := by
  calc
    _ ≤ |(rationalBoundedCosApprox q p : ℝ) - Real.cos (q : ℝ)| +
        |Real.cos (q : ℝ) - Real.cos x| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (rationalBoundedCosApprox_error q p)
      ((Real.abs_cos_sub_cos_le _ _).trans hq)

end

end MeyerGeneralProblem.StrongParity
