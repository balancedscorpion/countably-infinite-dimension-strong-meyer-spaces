module

public import MeyerGeneralProblem.Cardinal.Strong.PhaseDistance
public import MeyerGeneralProblem.Cardinal.Strong.SheetFlow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! An explicit real lift of the ORIGINAL Blaschke phase.
The arctangent denominator stays positive for the actual sheet parameters.
The formulas retain the native unit phase and quarter-phase conventions.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The strictly positive real denominator in the original phase lift. -/
def sheetLiftDenominator (a t : ℝ) : ℝ := 1 - a * Real.cos (2 * Real.pi * t)

/-- The literal real tangent used by the original phase correction. -/
def sheetLiftTangent (a t : ℝ) : ℝ :=
  a * Real.sin (2 * Real.pi * t) / sheetLiftDenominator a t

/-- A globally continuous real lift of the original Blaschke circle phase. -/
def sheetPhaseLift (a t : ℝ) : ℝ := t + Real.arctan (sheetLiftTangent a t) / Real.pi

theorem sheetLiftDenominator_pos {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    0 < sheetLiftDenominator a t := by
  have h := mul_le_mul_of_nonneg_left (Real.cos_le_one (2 * Real.pi * t)) ha
  dsimp [sheetLiftDenominator]
  nlinarith

theorem sheetPhaseLift_sub_bounds (a t : ℝ) :
    -(1 / 2) < sheetPhaseLift a t - t ∧ sheetPhaseLift a t - t < 1 / 2 := by
  have hl := Real.neg_pi_div_two_lt_arctan (sheetLiftTangent a t)
  have hu := Real.arctan_lt_pi_div_two (sheetLiftTangent a t)
  dsimp [sheetPhaseLift]
  constructor
  · rw [add_sub_cancel_left, lt_div_iff₀ Real.pi_pos]
    linarith
  · rw [add_sub_cancel_left, div_lt_iff₀ Real.pi_pos]
    linarith

theorem sheetPhaseLift_zero_parameter (t : ℝ) : sheetPhaseLift 0 t = t := by
  simp [sheetPhaseLift, sheetLiftTangent]

/-- The half-angle formula in the actual exponential unit phase. -/
theorem unitPhase_arctan_div_pi (q : ℝ) :
    unitPhase (Real.arctan q / Real.pi) =
      (1 + (q : ℂ) * Complex.I) / (1 - (q : ℂ) * Complex.I) := by
  have hd : (1 - (q : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  have hspos : 0 < 1 + q ^ 2 := by positivity
  have hs : Real.sqrt (1 + q ^ 2) ≠ 0 := (Real.sqrt_pos.2 hspos).ne'
  have hs2 := Real.sq_sqrt hspos.le
  unfold unitPhase
  rw [show 2 * Real.pi * (Real.arctan q / Real.pi) = 2 * Real.arctan q by
    field_simp, Complex.exp_ofReal_mul_I]
  apply (eq_div_iff hd).mpr
  apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  · rw [Real.cos_two_mul', Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan]
    field_simp
    rw [hs2]
    ring
  · rw [Real.cos_two_mul', Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan]
    field_simp
    rw [hs2]
    ring

/-- Rescaling the literal half-angle quotient uses only a nonzero real denominator. -/
theorem real_halfAngle_quotient {d : ℝ} (hd : d ≠ 0) (y : ℝ) :
    (1 + ((y / d : ℝ) : ℂ) * Complex.I) / (1 - ((y / d : ℝ) : ℂ) * Complex.I) =
      ((d : ℂ) + (y : ℂ) * Complex.I) / ((d : ℂ) - (y : ℂ) * Complex.I) := by
  have hdc : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hD : (d : ℂ) - (y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact hd hr
  have hQ : (1 - ((y / d : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  simp only [Complex.ofReal_div]
  field_simp [hdc, hD, hQ]

/-- The lift exponentiates to the literal ORIGINAL Blaschke factor. -/
theorem sheetPhaseLift_unitPhase_mul {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    unitPhase (sheetPhaseLift a t) * (1 - (a : ℂ) * unitPhase t) = unitPhase t - a := by
  have hd : sheetLiftDenominator a t ≠ 0 := (sheetLiftDenominator_pos ha ha1 t).ne'
  have hw : unitPhase t = (Real.cos (2 * Real.pi * t) : ℂ) +
      (Real.sin (2 * Real.pi * t) : ℂ) * Complex.I := Complex.exp_ofReal_mul_I _
  have hden : (sheetLiftDenominator a t : ℂ) -
      (a * Real.sin (2 * Real.pi * t) : ℝ) * Complex.I = 1 - (a : ℂ) * unitPhase t := by
    rw [hw]
    dsimp [sheetLiftDenominator]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one]
    ring
  have hnum : (sheetLiftDenominator a t : ℂ) +
      (a * Real.sin (2 * Real.pi * t) : ℝ) * Complex.I =
      1 - (a : ℂ) * (starRingEnd ℂ) (unitPhase t) := by
    rw [hw]
    dsimp [sheetLiftDenominator]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one]
    ring
  have hn : 1 - (a : ℂ) * unitPhase t ≠ 0 := by
    intro h
    rw [← hden] at h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero] at hr
    exact hd hr
  have hunit : unitPhase t * (starRingEnd ℂ) (unitPhase t) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, unitPhase_norm]
    norm_num
  rw [sheetPhaseLift, unitPhase_add, unitPhase_arctan_div_pi, sheetLiftTangent,
    real_halfAngle_quotient hd, hden, hnum, mul_assoc, div_mul_cancel₀ _ hn]
  linear_combination -(a : ℂ) * hunit

end

end MeyerGeneralProblem.StrongParity
