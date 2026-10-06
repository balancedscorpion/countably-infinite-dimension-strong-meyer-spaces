module

public import MeyerGeneralProblem.Cardinal.Strong.RationalArctan
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! Executable rational pi intervals from the ACTUAL arctangent evaluator. -/

namespace MeyerGeneralProblem.StrongParity

/-- A finite rational approximation to pi at the requested binary precision. -/
def rationalPiApprox (p : ℕ) : ℚ := 4 * rationalArctanApprox 1 (p + 2)

/-- The certified rational lower endpoint for the actual pi. -/
def rationalPiLower (p : ℕ) : ℚ := rationalPiApprox p - rationalBinaryRadius p

/-- An executable rational approximation of the reciprocal of actual pi. -/
def rationalInvPiApprox (p : ℕ) : ℚ := (rationalPiApprox p)⁻¹

noncomputable section

/-- Every emitted value is an upper bound on the ACTUAL pi. -/
theorem rationalPiApprox_upper (p : ℕ) : Real.pi ≤ (rationalPiApprox p : ℝ) := by
  have h := rationalArctanApprox_upper_nonneg (q := 1) (by norm_num) (p + 2)
  rw [Rat.cast_one, Real.arctan_one] at h
  dsimp [rationalPiApprox]
  push_cast
  linarith

/-- The error is certified for EVERY requested binary precision. -/
theorem rationalPiApprox_error (p : ℕ) :
    |(rationalPiApprox p : ℝ) - Real.pi| ≤ 1 / (2 : ℝ) ^ p := by
  have h := rationalArctanApprox_error 1 (p + 2)
  rw [Rat.cast_one, Real.arctan_one] at h
  have hi : (rationalPiApprox p : ℝ) - Real.pi =
      4 * ((rationalArctanApprox 1 (p + 2) : ℝ) - Real.pi / 4) := by
    simp only [rationalPiApprox, Rat.cast_mul, Rat.cast_ofNat]
    ring
  rw [hi, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc
    _ ≤ 4 * (1 / (2 : ℝ) ^ (p + 2)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by rw [pow_add]; norm_num; field_simp

/-- Actual pi lies in the emitted rational interval. -/
theorem rationalPi_interval (p : ℕ) :
    (rationalPiLower p : ℝ) ≤ Real.pi ∧ Real.pi ≤ (rationalPiApprox p : ℝ) := by
  have h := (abs_le.mp (rationalPiApprox_error p)).2
  simp only [rationalPiLower, Rat.cast_sub, rationalBinaryRadius_cast]
  exact ⟨by linarith, rationalPiApprox_upper p⟩

/-- The upper approximant is safely positive at ALL precisions. -/
theorem rationalPiApprox_gt_three (p : ℕ) : (3 : ℝ) < (rationalPiApprox p : ℝ) :=
  lt_of_lt_of_le Real.pi_gt_three (rationalPiApprox_upper p)

theorem rationalPiApprox_ne_zero (p : ℕ) : rationalPiApprox p ≠ 0 := by
  have h := rationalPiApprox_gt_three p
  intro hz
  rw [hz, Rat.cast_zero] at h
  norm_num at h

/-- Safe inversion retains a proved finite precision error. -/
theorem rationalInvPiApprox_error (p : ℕ) :
    |(rationalInvPiApprox p : ℝ) - Real.pi⁻¹| ≤ 1 / (9 * (2 : ℝ) ^ p) := by
  have hp : 0 < (rationalPiApprox p : ℝ) := by linarith [rationalPiApprox_gt_three p]
  have hd : 9 ≤ (rationalPiApprox p : ℝ) * Real.pi := by
    nlinarith [rationalPiApprox_gt_three p, Real.pi_gt_three]
  have hi : (rationalPiApprox p : ℝ)⁻¹ - Real.pi⁻¹ =
      (Real.pi - (rationalPiApprox p : ℝ)) / ((rationalPiApprox p : ℝ) * Real.pi) := by
    field_simp
  simp only [rationalInvPiApprox, Rat.cast_inv]
  rw [hi, abs_div, abs_mul, abs_of_pos hp, abs_of_pos Real.pi_pos, abs_sub_comm]
  calc
    _ ≤ (1 / (2 : ℝ) ^ p) / ((rationalPiApprox p : ℝ) * Real.pi) :=
      div_le_div_of_nonneg_right (rationalPiApprox_error p) (mul_pos hp Real.pi_pos).le
    _ ≤ (1 / (2 : ℝ) ^ p) / 9 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
    _ = _ := by field_simp

end

end MeyerGeneralProblem.StrongParity
