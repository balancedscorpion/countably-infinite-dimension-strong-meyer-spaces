module

public import MeyerGeneralProblem.Cardinal.Strong.ComplexSheetFlow
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Quantitative spacing of the actual real sheet roots

The literal derivative is a finite sum of exponential phases. Its
global Lipschitz estimate and nonzero lower bound at roots control the
Taylor remainder and force a uniform positive distance between roots.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem unitPhase_norm_sub_upper (t s : ℝ) :
    ‖unitPhase t - unitPhase s‖ ≤ 2 * Real.pi * |t - s| := by
  rw [unitPhase_difference_norm]
  unfold unitPhase
  rw [mul_comm _ Complex.I]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (t - s))
  simpa [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos, mul_assoc] using h

theorem unitPhase_affine_norm_sub_upper {r : ℝ} (hr : 0 ≤ r) (c y x : ℝ) :
    ‖unitPhase (r * y + c) - unitPhase (r * x + c)‖ ≤
      2 * Real.pi * r * |y - x| := by
  have h := unitPhase_norm_sub_upper (r * y + c) (r * x + c)
  rw [show r * y + c - (r * x + c) = r * (y - x) by ring,
    abs_mul, abs_of_nonneg hr] at h
  simpa only [mul_assoc] using h

/-- The global Lipschitz constant obtained from the three actual phase terms. -/
def sheetDerivativeLipschitzConstant (a : ℝ) : ℝ :=
  (2 * Real.pi) ^ 2 * (a * (1 + beta ^ 2) + (1 + beta) ^ 2)

theorem sheetDerivativeLipschitzConstant_pos {a : ℝ} (ha : 0 ≤ a) :
    0 < sheetDerivativeLipschitzConstant a := by
  have hb : 0 < beta := by linarith [beta_between_three_four]
  unfold sheetDerivativeLipschitzConstant
  positivity

/-- The product of the two phases is combined into its literal third frequency. -/
theorem sheetFlow_deriv_formula (a x : ℝ) :
    deriv (sheetFlow a) x = (2 * Real.pi : ℝ) * Complex.I *
      ((a : ℂ) * unitPhase x - (a * beta : ℝ) * unitPhase (beta * x - 1 / 4) -
        (1 + beta : ℝ) * unitPhase ((1 + beta) * x - 1 / 4)) := by
  rw [(sheetFlow_hasDerivAt a x).deriv]
  have hprod : unitPhase x * unitPhase (beta * x - 1 / 4) =
      unitPhase ((1 + beta) * x - 1 / 4) := by
    rw [← unitPhase_add]
    congr 1
    ring
  simp only [sheetTorusDerivative, hprod]
  push_cast
  ring

/-- A global derivative estimate on the complete actual real line. -/
theorem sheetFlow_deriv_norm_sub_le {a : ℝ} (ha : 0 ≤ a) (y x : ℝ) :
    ‖deriv (sheetFlow a) y - deriv (sheetFlow a) x‖ ≤
      sheetDerivativeLipschitzConstant a * |y - x| := by
  have hb : 0 < beta := by linarith [beta_between_three_four]
  have hZ := unitPhase_norm_sub_upper y x
  have hW := unitPhase_affine_norm_sub_upper hb.le (-(1 / 4)) y x
  have hV := unitPhase_affine_norm_sub_upper (by linarith : 0 ≤ 1 + beta) (-(1 / 4)) y x
  simp only [← sub_eq_add_neg] at hW hV
  have hid : deriv (sheetFlow a) y - deriv (sheetFlow a) x =
      (2 * Real.pi : ℝ) * Complex.I *
        ((a : ℂ) * (unitPhase y - unitPhase x) -
          (a * beta : ℝ) * (unitPhase (beta * y - 1 / 4) - unitPhase (beta * x - 1 / 4)) -
          (1 + beta : ℝ) * (unitPhase ((1 + beta) * y - 1 / 4) -
            unitPhase ((1 + beta) * x - 1 / 4))) := by
    rw [sheetFlow_deriv_formula, sheetFlow_deriv_formula]
    ring
  rw [hid, norm_mul]
  have htri : ‖(a : ℂ) * (unitPhase y - unitPhase x) -
        (a * beta : ℝ) * (unitPhase (beta * y - 1 / 4) - unitPhase (beta * x - 1 / 4)) -
        (1 + beta : ℝ) * (unitPhase ((1 + beta) * y - 1 / 4) -
          unitPhase ((1 + beta) * x - 1 / 4))‖ ≤
      a * ‖unitPhase y - unitPhase x‖ +
        a * beta * ‖unitPhase (beta * y - 1 / 4) - unitPhase (beta * x - 1 / 4)‖ +
        (1 + beta) * ‖unitPhase ((1 + beta) * y - 1 / 4) -
          unitPhase ((1 + beta) * x - 1 / 4)‖ := by
    calc
      _ ≤ ‖(a : ℂ) * (unitPhase y - unitPhase x) -
          (a * beta : ℝ) * (unitPhase (beta * y - 1 / 4) - unitPhase (beta * x - 1 / 4))‖ +
          ‖(1 + beta : ℝ) * (unitPhase ((1 + beta) * y - 1 / 4) -
            unitPhase ((1 + beta) * x - 1 / 4))‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ) * (unitPhase y - unitPhase x)‖ +
          ‖(a * beta : ℝ) * (unitPhase (beta * y - 1 / 4) - unitPhase (beta * x - 1 / 4))‖ +
          ‖(1 + beta : ℝ) * (unitPhase ((1 + beta) * y - 1 / 4) -
            unitPhase ((1 + beta) * x - 1 / 4))‖ := by gcongr; exact norm_sub_le _ _
      _ = _ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
          abs_of_pos hb, abs_of_nonneg (by linarith : 0 ≤ 1 + beta)]
  calc
    _ ≤ ‖(2 * Real.pi : ℝ) * Complex.I‖ *
        (a * ‖unitPhase y - unitPhase x‖ +
          a * beta * ‖unitPhase (beta * y - 1 / 4) - unitPhase (beta * x - 1 / 4)‖ +
          (1 + beta) * ‖unitPhase ((1 + beta) * y - 1 / 4) -
            unitPhase ((1 + beta) * x - 1 / 4)‖) :=
      mul_le_mul_of_nonneg_left htri (norm_nonneg _)
    _ ≤ (2 * Real.pi) * (a * (2 * Real.pi * |y - x|) +
        a * beta * (2 * Real.pi * beta * |y - x|) +
        (1 + beta) * (2 * Real.pi * (1 + beta) * |y - x|)) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
        abs_of_pos Real.pi_pos]
      norm_num only
      gcongr
    _ = _ := by unfold sheetDerivativeLipschitzConstant; ring

/-- The derivative estimate controls the complete actual Taylor remainder. -/
theorem sheetFlow_remainder_norm_le {a : ℝ} (ha : 0 ≤ a) (y x : ℝ) :
    ‖sheetFlow a y - sheetFlow a x - (y - x : ℝ) * deriv (sheetFlow a) x‖ ≤
      sheetDerivativeLipschitzConstant a * |y - x| ^ 2 := by
  let g : ℝ → ℂ := fun t => sheetFlow a t - sheetFlow a x - (t - x : ℝ) * deriv (sheetFlow a) x
  have hf (t : ℝ) : HasDerivAt (sheetFlow a) (deriv (sheetFlow a) t) t :=
    (sheetFlow_hasDerivAt a t).differentiableAt.hasDerivAt
  have hg (t : ℝ) : HasDerivAt g (deriv (sheetFlow a) t - deriv (sheetFlow a) x) t := by
    have ht := ((hasDerivAt_id t).sub_const x).ofReal_comp.mul_const (deriv (sheetFlow a) x)
    convert! ((hf t).sub_const (sheetFlow a x)).sub ht using 1
    simp
  have hbound : ∀ t ∈ Metric.closedBall x |y - x|,
      ‖deriv (sheetFlow a) t - deriv (sheetFlow a) x‖ ≤
        sheetDerivativeLipschitzConstant a * |y - x| := by
    intro t ht
    have ht' : |t - x| ≤ |y - x| := by simpa [Metric.mem_closedBall, Real.dist_eq] using ht
    exact (sheetFlow_deriv_norm_sub_le ha t x).trans
      (mul_le_mul_of_nonneg_left ht' (sheetDerivativeLipschitzConstant_pos ha).le)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := x) (y := y)
    (fun t ht => (hg t).hasDerivWithinAt) hbound (convex_closedBall x |y - x|)
    (by simp [Metric.mem_closedBall])
    (by simp [Metric.mem_closedBall, Real.dist_eq])
  simpa [g, Real.norm_eq_abs, pow_two, mul_assoc] using hmv

theorem sheetFlow_deriv_norm_lower {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hroot : sheetFlow a x = 0) :
    2 * Real.pi * (1 - a) ≤ ‖deriv (sheetFlow a) x‖ := by
  rw [(sheetFlow_hasDerivAt a x).deriv, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  exact mul_le_mul_of_nonneg_left
    (sheetTorusDerivative_norm_lower ha ha1 (unitPhase_norm _) hroot) (by positivity)

/-- The explicit positive separation forced by the actual derivative bounds. -/
def sheetRootSpacing (a : ℝ) : ℝ :=
  (2 * Real.pi * (1 - a)) / sheetDerivativeLipschitzConstant a

theorem sheetRootSpacing_pos {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    0 < sheetRootSpacing a := by
  unfold sheetRootSpacing
  exact div_pos (by positivity) (sheetDerivativeLipschitzConstant_pos ha)

/-- Distinct actual real roots have a uniform positive separation. -/
theorem sheetFlow_roots_separated {a x y : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hx : sheetFlow a x = 0) (hy : sheetFlow a y = 0) (hxy : x ≠ y) :
    sheetRootSpacing a ≤ |x - y| := by
  have hrem := sheetFlow_remainder_norm_le ha y x
  have hrpos : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr hxy.symm)
  rw [hx, hy, sub_self, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hrem
  have hfirst : ‖deriv (sheetFlow a) x‖ ≤ sheetDerivativeLipschitzConstant a * |y - x| := by
    apply (mul_le_mul_iff_right₀ hrpos).mp
    nlinarith [hrem]
  have hlow := sheetFlow_deriv_norm_lower ha ha1 hx
  rw [sheetRootSpacing, abs_sub_comm]
  apply (div_le_iff₀ (sheetDerivativeLipschitzConstant_pos ha)).mpr
  nlinarith

end

end MeyerGeneralProblem.StrongParity
