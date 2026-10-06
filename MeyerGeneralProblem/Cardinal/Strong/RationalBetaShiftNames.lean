module

public import MeyerGeneralProblem.Cardinal.Strong.RationalUnitPhaseNames
public import MeyerGeneralProblem.Cardinal.Strong.RationalBetaApprox

@[expose] public section

/-! Ordinary binary names for the actual second original flow coordinate
beta*x - 1/4. The finite input-size and multiplication budgets are internal. -/

namespace MeyerGeneralProblem.StrongParity

/-- Computed input/beta multiplication sensitivity. -/
def rationalBetaShiftSensitivity (name : ℕ → ℚ) : ℕ := 5 + rationalRealNameSize name

/-- The literal rational second-coordinate program at specified entry precision. -/
def rationalNamedBetaShiftAt (name : ℕ → ℚ) (p : ℕ) : ℚ :=
  rationalBetaApprox p * name p - 1 / 4

/-- Internally budgeted binary name of the actual quarter-shifted beta coordinate. -/
def rationalNamedBetaShift (name : ℕ → ℚ) (p : ℕ) : ℚ :=
  rationalNamedBetaShiftAt name (p + rationalBetaShiftSensitivity name)

noncomputable section

/-- Every fixed-beta approximant satisfies the safe computed product bound. -/
theorem rationalBetaApprox_abs_le_five (p : ℕ) : |(rationalBetaApprox p : ℝ)| ≤ 5 := by
  have he := rationalBetaApprox_error p
  have hb : 1 / (2 : ℝ) ^ p ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ p)
  have h := abs_add_le ((rationalBetaApprox p : ℝ) - beta) beta
  rw [sub_add_cancel, abs_of_pos (by linarith [beta_between_three_four] : 0 < beta)] at h
  linarith [beta_between_three_four]

/-- All beta/input errors are included in the literal second-coordinate program. -/
theorem rationalNamedBetaShiftAt_error (name : ℕ → ℚ) {x : ℝ}
    (hname : ∀ p, |(name p : ℝ) - x| ≤ 1 / (2 : ℝ) ^ p) (p : ℕ) :
    |(rationalNamedBetaShiftAt name p : ℝ) - (beta * x - 1 / 4)| ≤
      (rationalBetaShiftSensitivity name : ℝ) * (1 / (2 : ℝ) ^ p) := by
  have heq : (rationalNamedBetaShiftAt name p : ℝ) - (beta * x - 1 / 4) =
      (rationalBetaApprox p : ℝ) * ((name p : ℝ) - x) +
        ((rationalBetaApprox p : ℝ) - beta) * x := by
    simp only [rationalNamedBetaShiftAt, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat]
    ring
  rw [heq]
  calc
    _ ≤ |(rationalBetaApprox p : ℝ) * ((name p : ℝ) - x)| +
      |((rationalBetaApprox p : ℝ) - beta) * x| := abs_add_le _ _
    _ ≤ 5 * (1 / (2 : ℝ) ^ p) + (1 / (2 : ℝ) ^ p) * (rationalRealNameSize name : ℝ) := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul (rationalBetaApprox_abs_le_five p) (hname p) (abs_nonneg _) (by norm_num))
        (mul_le_mul (rationalBetaApprox_error p) (rationalRealNameSize_bound name hname)
          (abs_nonneg _) (by positivity))
    _ = _ := by simp only [rationalBetaShiftSensitivity]; push_cast; ring

/-- The second flow coordinate has the requested binary precision, supplied internally. -/
theorem rationalNamedBetaShift_error (name : ℕ → ℚ) {x : ℝ}
    (hname : ∀ p, |(name p : ℝ) - x| ≤ 1 / (2 : ℝ) ^ p) (p : ℕ) :
    |(rationalNamedBetaShift name p : ℝ) - (beta * x - 1 / 4)| ≤ 1 / (2 : ℝ) ^ p :=
  (rationalNamedBetaShiftAt_error name hname (p + rationalBetaShiftSensitivity name)).trans
    (integer_sensitivity_binary_shift (rationalBetaShiftSensitivity name) p)

end

end MeyerGeneralProblem.StrongParity
