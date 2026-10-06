module

public import MeyerGeneralProblem.Cardinal.Strong.PolydiskBound
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-! Literal geometric coefficients of the original sheet reciprocal.
The disk norm and denominator bounds are proved on the closed unit disk;
the geometric series then represents the actual rational function. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The original Blaschke quotient, with the original sheet parameter. -/
def sheetBlaschke (a : ℝ) (W : ℂ) : ℂ := (W - a) / (1 - a * W)

theorem sheetDiskDenominator_norm_lower {a : ℝ} (ha : 0 ≤ a) {W : ℂ}
    (hW : ‖W‖ ≤ 1) : 1 - a ≤ ‖(1 : ℂ) - a * W‖ := by
  have ham : ‖(a : ℂ) * W‖ ≤ a := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left hW ha).trans_eq (mul_one a)
  have h := norm_sub_norm_le (1 : ℂ) (a * W)
  rw [norm_one] at h
  linarith

theorem sheetDiskDenominator_ne_zero {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {W : ℂ} (hW : ‖W‖ ≤ 1) : (1 : ℂ) - a * W ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le (sub_pos.mpr ha1)
    (sheetDiskDenominator_norm_lower ha hW))

theorem sheetBlaschke_norm_le_one {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {W : ℂ} (hW : ‖W‖ ≤ 1) : ‖sheetBlaschke a W‖ ≤ 1 := by
  have hsqW : ‖W‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg W]
  have hfactor : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hdiff := blaschke_normSq_difference a W
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq] at hdiff
  have hprod : (1 - a ^ 2) * (‖W‖ ^ 2 - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfactor (by linarith)
  have hWa : ‖W - a‖ ≤ ‖(1 : ℂ) - a * W‖ := by
    nlinarith [norm_nonneg (W - a), norm_nonneg ((1 : ℂ) - a * W)]
  have hden : 0 < ‖(1 : ℂ) - a * W‖ :=
    lt_of_lt_of_le (sub_pos.mpr ha1) (sheetDiskDenominator_norm_lower ha hW)
  rw [sheetBlaschke, norm_div, div_le_iff₀ hden, one_mul]
  exact hWa

theorem sheetPolynomial_blaschke_factor {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {W : ℂ} (hW : ‖W‖ ≤ 1) (Z : ℂ) :
    sheetPolynomial a Z W = (1 - a * W) * (1 - Z * sheetBlaschke a W) := by
  have hd := sheetDiskDenominator_ne_zero ha ha1 hW
  unfold sheetPolynomial sheetBlaschke
  field_simp [hd]
  ring

/-- The actual Z coefficient of a single original reciprocal sheet. -/
def sheetZCoefficient (a : ℝ) (k : ℕ) (W : ℂ) : ℂ :=
  sheetBlaschke a W ^ k / (1 - a * W)

theorem sheetZCoefficient_norm_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (k : ℕ) {W : ℂ} (hW : ‖W‖ ≤ 1) :
    ‖sheetZCoefficient a k W‖ ≤ 1 / (1 - a) := by
  have hpow : ‖sheetBlaschke a W‖ ^ k ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (sheetBlaschke_norm_le_one ha ha1 hW)
  calc
    _ = ‖sheetBlaschke a W‖ ^ k / ‖(1 : ℂ) - a * W‖ := by
      rw [sheetZCoefficient, norm_div, norm_pow]
    _ ≤ 1 / ‖(1 : ℂ) - a * W‖ :=
      div_le_div_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ _ := one_div_le_one_div_of_le (sub_pos.mpr ha1)
      (sheetDiskDenominator_norm_lower ha hW)

theorem sheetZCoefficient_differentiableOn {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (k : ℕ) : DifferentiableOn ℂ (sheetZCoefficient a k) (Metric.closedBall 0 1) := by
  intro W hW
  have hWnorm : ‖W‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hW
  have hd := sheetDiskDenominator_ne_zero ha ha1 hWnorm
  have hD : DifferentiableAt ℂ (fun W : ℂ => 1 - (a : ℂ) * W) W :=
    (differentiableAt_const (1 : ℂ)).sub
      ((differentiableAt_const (a : ℂ)).mul differentiableAt_id)
  have hB : DifferentiableAt ℂ (sheetBlaschke a) W :=
    (differentiableAt_id.sub (differentiableAt_const (a : ℂ))).div hD hd
  exact ((hB.pow k).div hD hd).differentiableWithinAt

/-- The original reciprocal is represented by its actual geometric Z series. -/
theorem sheetZCoefficient_hasSum {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {W Z : ℂ} (hW : ‖W‖ ≤ 1) (hZ : ‖Z‖ < 1) :
    HasSum (fun k : ℕ => sheetZCoefficient a k W * Z ^ k)
      (sheetPolynomial a Z W)⁻¹ := by
  have hB := sheetBlaschke_norm_le_one ha ha1 hW
  have hr : ‖Z * sheetBlaschke a W‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hB (norm_nonneg Z)).trans_eq
      (mul_one ‖Z‖)) hZ
  have hs := (hasSum_geometric_of_norm_lt_one hr).mul_left ((1 - a * W : ℂ)⁻¹)
  rw [sheetPolynomial_blaschke_factor ha ha1 hW Z, mul_inv_rev]
  simpa only [sheetZCoefficient, div_eq_mul_inv, mul_pow, mul_comm,
    mul_left_comm, mul_assoc] using hs

end

end MeyerGeneralProblem.StrongParity
