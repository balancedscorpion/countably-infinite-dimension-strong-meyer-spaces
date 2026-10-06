module

public import MeyerGeneralProblem.Cardinal.Strong.ProductSeparation

@[expose] public section

/-! The literal original denominator on the complex polydisk has the
analytic lower bound needed for polynomial upper spectral coefficients.
This module proves the bound itself, not a Fourier or Cauchy certificate. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem sheetPolynomial_polydisk_norm_lower {a r : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hr : 0 ≤ r) (hr1 : r < 1) {Z W : ℂ} (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r) :
    (1 - a) * (1 - r) ≤ ‖sheetPolynomial a Z W‖ := by
  have hW1 : ‖W‖ ≤ 1 := hW.trans hr1.le
  have hsqW : ‖W‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg W]
  have hfactor : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hdiff := blaschke_normSq_difference a W
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hdiff
  have hprod : (1 - a ^ 2) * (‖W‖ ^ 2 - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfactor (by linarith)
  have hWa : ‖W - a‖ ≤ ‖(1 : ℂ) - a * W‖ := by
    nlinarith [norm_nonneg (W - a), norm_nonneg ((1 : ℂ) - a * W)]
  have haW : ‖(a : ℂ) * W‖ ≤ a := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left hW1 ha).trans_eq (mul_one a)
  have hden : 1 - a ≤ ‖(1 : ℂ) - a * W‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (a * W)
    rw [norm_one] at h
    linarith
  have hZWa : ‖Z * (W - a)‖ ≤ r * ‖(1 : ℂ) - a * W‖ := by
    rw [norm_mul]
    exact mul_le_mul hZ hWa (norm_nonneg _) hr
  have hp : sheetPolynomial a Z W = ((1 : ℂ) - a * W) - Z * (W - a) := by
    unfold sheetPolynomial
    ring
  calc
    _ ≤ ‖(1 : ℂ) - a * W‖ * (1 - r) :=
      mul_le_mul_of_nonneg_right hden (sub_nonneg.mpr hr1.le)
    _ ≤ ‖(1 : ℂ) - a * W‖ - ‖Z * (W - a)‖ := by nlinarith
    _ ≤ ‖sheetPolynomial a Z W‖ := by rw [hp]; exact norm_sub_norm_le _ _

/-- The explicit nonzero constant for the original finite product polydisk bound. -/
def productPolydiskConstant (s : ℕ) : ℝ := ∏ i : Fin s, (1 - productSheetParameter s i)

theorem productPolydiskConstant_pos (s : ℕ) : 0 < productPolydiskConstant s := by
  apply Finset.prod_pos
  intro i _
  exact sub_pos.mpr (productSheetParameter_bounds s i).2

theorem productSheetPolynomial_polydisk_norm_lower (s : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) {Z W : ℂ} (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r) :
    productPolydiskConstant s * (1 - r) ^ s ≤ ‖productSheetPolynomial s Z W‖ := by
  have hp : productPolydiskConstant s * (1 - r) ^ s =
      ∏ i : Fin s, (1 - productSheetParameter s i) * (1 - r) := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, productPolydiskConstant]
  rw [hp, productSheetPolynomial, norm_prod]
  apply Finset.prod_le_prod₀
  · intro i _
    exact mul_nonneg (sub_nonneg.mpr (productSheetParameter_bounds s i).2.le)
      (sub_nonneg.mpr hr1.le)
  · intro i _
    exact sheetPolynomial_polydisk_norm_lower (productSheetParameter_bounds s i).1.le
      (productSheetParameter_bounds s i).2 hr hr1 hZ hW

/-- Literal denominator nonvanishing throughout each closed smaller polydisk. -/
theorem productSheetPolynomial_polydisk_ne_zero (s : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) {Z W : ℂ} (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r) :
    productSheetPolynomial s Z W ≠ 0 := by
  have hpos : 0 < productPolydiskConstant s * (1 - r) ^ s :=
    mul_pos (productPolydiskConstant_pos s) (pow_pos (sub_pos.mpr hr1) _)
  exact norm_pos_iff.mp (lt_of_lt_of_le hpos
    (productSheetPolynomial_polydisk_norm_lower s hr hr1 hZ hW))

end

end MeyerGeneralProblem.StrongParity
