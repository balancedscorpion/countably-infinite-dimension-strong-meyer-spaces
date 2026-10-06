module

public import MeyerGeneralProblem.Cardinal.Strong.RationalTrigPerturbation
public import MeyerGeneralProblem.Cardinal.Strong.RationalPi
public import MeyerGeneralProblem.Cardinal.Strong.CompactPhaseEvaluationBounds

@[expose] public section

/-! Actual executable original tangent values and certified safe quotient errors. -/

namespace MeyerGeneralProblem.StrongParity

/-- The actual finite rational approximation of the original angular argument. -/
def rationalSheetAngle (t : ℚ) (p : ℕ) : ℚ := 2 * rationalPiApprox p * t

/-- The computed positive denominator in the original phase formula. -/
def rationalSheetDenominator (a t : ℚ) (p : ℕ) : ℚ :=
  1 - a * rationalBoundedCosApprox (rationalSheetAngle t p) p

/-- The executable literal original tangent, using safe bounded trigonometric values. -/
def rationalSheetTangent (a t : ℚ) (p : ℕ) : ℚ :=
  a * rationalBoundedSinApprox (rationalSheetAngle t p) p / rationalSheetDenominator a t p

noncomputable section

/-- Safe quotient error when both denominators and the actual quotient are bounded. -/
theorem half_denominator_quotient_error {u v d e delta : ℝ}
    (hd : 1 / 2 ≤ d) (he : 1 / 2 ≤ e) (hv : |v / e| ≤ 1)
    (hu : |u - v| ≤ delta / 2) (he' : |e - d| ≤ delta / 2) :
    |u / d - v / e| ≤ 2 * delta := by
  have hdpos : 0 < d := by linarith
  have hepos : 0 < e := by linarith
  have hdelta : 0 ≤ delta := by linarith [abs_nonneg (u - v)]
  have hi : u / d - v / e = ((u - v) + (v / e) * (e - d)) / d := by
    field_simp; ring
  rw [hi, abs_div, abs_of_pos hdpos]
  calc
    _ ≤ (|u - v| + |v / e| * |e - d|) / d := by
      apply div_le_div_of_nonneg_right _ hdpos.le
      simpa only [abs_mul] using abs_add_le (u - v) ((v / e) * (e - d))
    _ ≤ (delta / 2 + 1 * (delta / 2)) / d := by
      apply div_le_div_of_nonneg_right _ hdpos.le
      exact add_le_add hu (mul_le_mul hv he' (abs_nonneg _) (by norm_num))
    _ = delta / d := by ring
    _ ≤ 2 * delta := (div_le_iff₀ hdpos).mpr (by nlinarith)

/-- The computed original angle approximates its ACTUAL pi-based argument. -/
theorem rationalSheetAngle_error (t : ℚ) (p : ℕ) :
    |(rationalSheetAngle t p : ℝ) - 2 * Real.pi * (t : ℝ)| ≤
      2 * |(t : ℝ)| / (2 : ℝ) ^ p := by
  have hi : (rationalSheetAngle t p : ℝ) - 2 * Real.pi * (t : ℝ) =
      2 * ((rationalPiApprox p : ℝ) - Real.pi) * (t : ℝ) := by
    simp only [rationalSheetAngle, Rat.cast_mul, Rat.cast_ofNat]
    ring
  rw [hi, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * (1 / (2 : ℝ) ^ p) * |(t : ℝ)| := by
      gcongr
      exact rationalPiApprox_error p
    _ = _ := by ring

theorem rationalSheetSin_error (t : ℚ) (p : ℕ) :
    |(rationalBoundedSinApprox (rationalSheetAngle t p) p : ℝ) -
      Real.sin (2 * Real.pi * (t : ℝ))| ≤ (1 + 2 * |(t : ℝ)|) / (2 : ℝ) ^ p := by
  apply (rationalBoundedSinApprox_real_input_error _ _ (rationalSheetAngle_error t p)).trans_eq
  ring

theorem rationalSheetCos_error (t : ℚ) (p : ℕ) :
    |(rationalBoundedCosApprox (rationalSheetAngle t p) p : ℝ) -
      Real.cos (2 * Real.pi * (t : ℝ))| ≤ (1 + 2 * |(t : ℝ)|) / (2 : ℝ) ^ p := by
  apply (rationalBoundedCosApprox_real_input_error _ _ (rationalSheetAngle_error t p)).trans_eq
  ring

/-- The COMPUTED denominator is safely positive at all precisions. -/
theorem rationalSheetDenominator_ge_half {a : ℚ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (t : ℚ) (p : ℕ) : (1 / 2 : ℝ) ≤ (rationalSheetDenominator a t p : ℝ) := by
  have hc : (rationalBoundedCosApprox (rationalSheetAngle t p) p : ℝ) ≤ 1 := by
    exact_mod_cast (rationalUnitClamp_bounds (rationalCosApprox (rationalSheetAngle t p) p)).2
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha1R : (a : ℝ) ≤ 1 / 2 := by
    have h : (a : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast ha1
    norm_num at h
    exact h
  simp only [rationalSheetDenominator, Rat.cast_sub, Rat.cast_one, Rat.cast_mul]
  nlinarith

/-- Multiplication by an actual compact-slot parameter keeps the error below half. -/
theorem compact_parameter_mul_abs_sub_le {a u v delta : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (h : |u - v| ≤ delta) :
    |a * u - a * v| ≤ delta / 2 := by
  have hd : 0 ≤ delta := (abs_nonneg _).trans h
  rw [← mul_sub, abs_mul, abs_of_nonneg ha]
  calc
    _ ≤ a * delta := mul_le_mul_of_nonneg_left h ha
    _ ≤ delta / 2 := by nlinarith

/-- Uniform actual error of the literal computed original tangent. -/
theorem rationalSheetTangent_error {a : ℚ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (t : ℚ) (p : ℕ) :
    |(rationalSheetTangent a t p : ℝ) - sheetLiftTangent a t| ≤
      2 * ((1 + 2 * |(t : ℝ)|) / (2 : ℝ) ^ p) := by
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha1R : (a : ℝ) ≤ 1 / 2 := by
    have h : (a : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast ha1
    norm_num at h
    exact h
  simp only [rationalSheetTangent, Rat.cast_div, Rat.cast_mul, sheetLiftTangent]
  apply half_denominator_quotient_error (rationalSheetDenominator_ge_half ha ha1 t p)
    (sheetLiftDenominator_compact_lower haR ha1R _) (sheetLiftTangent_compact_abs_le_one haR ha1R _)
  · exact compact_parameter_mul_abs_sub_le haR ha1R (rationalSheetSin_error t p)
  · have h := compact_parameter_mul_abs_sub_le haR ha1R (rationalSheetCos_error t p)
    simpa only [sheetLiftDenominator, rationalSheetDenominator, Rat.cast_sub, Rat.cast_one,
      Rat.cast_mul, sub_sub_sub_cancel_left, abs_sub_comm] using h

end

end MeyerGeneralProblem.StrongParity
