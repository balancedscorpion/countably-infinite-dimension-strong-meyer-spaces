module

public import MeyerGeneralProblem.Cardinal.Strong.ParityLimit
public import MeyerGeneralProblem.Cardinal.Strong.RationalArctan

@[expose] public section

/-! Actual finite rational values of the fixed original parity-Liouville constant. -/

namespace MeyerGeneralProblem.StrongParity

/-- The executable rational continuant of the original prescribed recurrence. -/
def rationalBetaApprox (p : ℕ) : ℚ := (numerator p : ℚ) / denominator p

noncomputable section

theorem rationalBetaApprox_cast (p : ℕ) : (rationalBetaApprox p : ℝ) = convergent p := by
  simp [rationalBetaApprox, convergent]

/-- Every requested precision has an actual computed rational value with a proved error. -/
theorem rationalBetaApprox_error (p : ℕ) :
    |(rationalBetaApprox p : ℝ) - beta| ≤ 1 / (2 : ℝ) ^ p := by
  rw [rationalBetaApprox_cast, abs_sub_comm]
  calc
    _ ≤ increment p := beta_sub_convergent_abs_le p
    _ ≤ (1 / 2 : ℝ) ^ p := increment_le_geometric p
    _ = _ := by rw [one_div_pow]

end

end MeyerGeneralProblem.StrongParity
