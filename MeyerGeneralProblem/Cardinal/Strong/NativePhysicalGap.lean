module

public import MeyerGeneralProblem.Cardinal.Strong.SheetSpacing
public import MeyerGeneralProblem.Cardinal.Strong.SheetProducts
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! A uniform gap about zero in the ACTUAL native physical carrier.
The proof uses the literal sheet value at zero and the actual phase Lipschitz
bounds, uniformly over all nonnegative sheet parameters. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem unitPhase_neg_quarter : unitPhase (-1 / 4) = -Complex.I := by
  unfold unitPhase
  have heq : ((2 * Real.pi * (-1 / 4) : ℝ) : ℂ) * Complex.I =
      -(Real.pi : ℂ) / 2 * Complex.I := by
    push_cast
    ring
  rw [heq, Complex.exp_neg_pi_div_two_mul_I]

theorem sheetFlow_zero (a : ℝ) : sheetFlow a 0 = (1 + (a : ℂ)) * (1 + Complex.I) := by
  have h0 : unitPhase 0 = 1 := by simp [unitPhase]
  have hw : unitPhase (beta * 0 - 1 / 4) = -Complex.I := by
    convert! unitPhase_neg_quarter using 1
    congr 1
    ring
  simp only [sheetFlow, sheetPolynomial, h0, hw]
  ring

/-- Actual phase terms give a uniform sheet Lipschitz estimate. -/
theorem sheetFlow_norm_sub_le {a : ℝ} (ha : 0 ≤ a) (y x : ℝ) :
    ‖sheetFlow a y - sheetFlow a x‖ ≤
      (1 + a) * (2 * Real.pi) * (1 + beta) * |y - x| := by
  have hb : 0 < beta := by linarith [beta_between_three_four]
  have hZ := unitPhase_norm_sub_upper y x
  have hW := unitPhase_affine_norm_sub_upper hb.le (-(1 / 4)) y x
  have hV := unitPhase_affine_norm_sub_upper (by linarith : 0 ≤ 1 + beta) (-(1 / 4)) y x
  simp only [← sub_eq_add_neg] at hW hV
  have hprod (t : ℝ) : unitPhase t * unitPhase (beta * t - 1 / 4) =
      unitPhase ((1 + beta) * t - 1 / 4) := by
    rw [← unitPhase_add]
    congr 1
    ring
  have hid : sheetFlow a y - sheetFlow a x =
      (a : ℂ) * (unitPhase y - unitPhase x) -
      (a : ℂ) * (unitPhase (beta * y - 1 / 4) - unitPhase (beta * x - 1 / 4)) -
      (unitPhase ((1 + beta) * y - 1 / 4) - unitPhase ((1 + beta) * x - 1 / 4)) := by
    simp only [sheetFlow, sheetPolynomial, hprod]
    ring
  rw [hid]
  calc
    _ ≤ ‖(a : ℂ) * (unitPhase y - unitPhase x) -
        (a : ℂ) * (unitPhase (beta * y - 1 / 4) - unitPhase (beta * x - 1 / 4))‖ +
        ‖unitPhase ((1 + beta) * y - 1 / 4) - unitPhase ((1 + beta) * x - 1 / 4)‖ :=
      norm_sub_le _ _
    _ ≤ ‖(a : ℂ) * (unitPhase y - unitPhase x)‖ +
        ‖(a : ℂ) * (unitPhase (beta * y - 1 / 4) - unitPhase (beta * x - 1 / 4))‖ +
        ‖unitPhase ((1 + beta) * y - 1 / 4) - unitPhase ((1 + beta) * x - 1 / 4)‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = a * ‖unitPhase y - unitPhase x‖ +
        a * ‖unitPhase (beta * y - 1 / 4) - unitPhase (beta * x - 1 / 4)‖ +
        ‖unitPhase ((1 + beta) * y - 1 / 4) - unitPhase ((1 + beta) * x - 1 / 4)‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ a * (2 * Real.pi * |y - x|) + a * (2 * Real.pi * beta * |y - x|) +
        2 * Real.pi * (1 + beta) * |y - x| := by gcongr
    _ = _ := by ring

/-- The literal uniform native gap from the accepted construction. -/
def nativePhysicalGap : ℝ := 1 / (8 * (1 + beta))

theorem nativePhysicalGap_pos : 0 < nativePhysicalGap := by
  have hb : 0 < beta := by linarith [beta_between_three_four]
  unfold nativePhysicalGap
  positivity

theorem sheetFlow_ne_zero_of_abs_le_nativePhysicalGap {a x : ℝ} (ha : 0 ≤ a)
    (hx : |x| ≤ nativePhysicalGap) : sheetFlow a x ≠ 0 := by
  intro hz
  have hb : 0 < 1 + beta := by linarith [beta_between_three_four]
  have ha1 : 0 < 1 + a := by linarith
  have hnorm : 1 + a ≤ ‖sheetFlow a 0‖ := by
    have h := Complex.re_le_norm (sheetFlow a 0)
    simpa [sheetFlow_zero, Complex.mul_re] using h
  have hbound := sheetFlow_norm_sub_le ha x 0
  rw [hz, zero_sub, norm_neg, sub_zero] at hbound
  have hsmall : (1 + a) * (2 * Real.pi) * (1 + beta) * |x| ≤
      (1 + a) * Real.pi / 4 := by
    calc
      _ ≤ (1 + a) * (2 * Real.pi) * (1 + beta) * nativePhysicalGap := by gcongr
      _ = _ := by unfold nativePhysicalGap; field_simp; ring
  have hstrict : (1 + a) * Real.pi / 4 < 1 + a := by
    nlinarith [Real.pi_lt_four]
  linarith

theorem realSheetProduct_ne_zero_of_abs_le_nativePhysicalGap (s : ℕ) {x : ℝ}
    (hx : |x| ≤ nativePhysicalGap) : realSheetProduct s x ≠ 0 := by
  unfold realSheetProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact sheetFlow_ne_zero_of_abs_le_nativePhysicalGap (productSheetParameter_bounds s i).1.le hx

theorem productSheetCarrier_abs_gt_nativePhysicalGap (s : ℕ)
    (x : (productSheetCarrier s).subtype) : nativePhysicalGap < |(x : ℝ)| := by
  by_contra h
  exact realSheetProduct_ne_zero_of_abs_le_nativePhysicalGap s (le_of_not_gt h) x.property

end

end MeyerGeneralProblem.StrongParity
