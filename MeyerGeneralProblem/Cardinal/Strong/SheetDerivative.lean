module

public import MeyerGeneralProblem.Cardinal.Strong.SheetSeparation

@[expose] public section

/-!
# The derivative denominator of an original sheet

The derivative in the irrational torus direction factors into its
Blaschke denominator and a strictly positive real factor at every root.
This establishes the uniform lower derivative bound used in the residue
estimate, before any root-counting or Fourier representation theorem.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- `Z ∂Z p + beta W ∂W p` for the literal sheet polynomial. -/
def sheetTorusDerivative (a : ℝ) (Z W : ℂ) : ℂ :=
  a * Z - Z * W + beta * (-a * W - Z * W)

/-- The positive circle derivative of the Blaschke argument lift. -/
def sheetCircleSpeed (a : ℝ) (W : ℂ) : ℝ :=
  (1 - a ^ 2) / Complex.normSq (W - a)

theorem unitCircle_sub_parameter_ne_zero {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {W : ℂ} (hW : ‖W‖ = 1) : W - a ≠ 0 := by
  intro h
  have heq := sub_eq_zero.mp h
  have hnorm := congrArg norm heq
  rw [hW, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] at hnorm
  linarith

theorem sheetCircleSpeed_pos {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {W : ℂ} (hW : ‖W‖ = 1) : 0 < sheetCircleSpeed a W := by
  unfold sheetCircleSpeed
  apply div_pos
  · nlinarith
  · exact Complex.normSq_pos.mpr (unitCircle_sub_parameter_ne_zero ha ha1 hW)

theorem unitCircle_blaschke_product (a : ℝ) {W : ℂ} (hW : ‖W‖ = 1) :
    (W - a) * (1 - a * W) = W * (Complex.normSq (W - a) : ℂ) := by
  have hunit : W * (starRingEnd ℂ) W = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hW]
    norm_num
  rw [← Complex.mul_conj]
  simp only [map_sub, Complex.conj_ofReal]
  linear_combination ((a : ℂ) - W) * hunit

/-- The derivative factorization retains the original real circle speed. -/
theorem sheetTorusDerivative_at_root {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {Z W : ℂ} (hW : ‖W‖ = 1) (hroot : sheetPolynomial a Z W = 0) :
    sheetTorusDerivative a Z W =
      -(1 - (a : ℂ) * W) * (1 + (beta * sheetCircleSpeed a W : ℝ)) := by
  have hd := unitCircle_sub_parameter_ne_zero ha ha1 hW
  have hdR : Complex.normSq (W - a) ≠ 0 :=
    (Complex.normSq_pos.mpr hd).ne'
  have hdC : (Complex.normSq (W - a) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdR
  have hprod := unitCircle_blaschke_product a hW
  have hza : (a + Z) * (W - a) = (1 - a ^ 2 : ℝ) := by
    dsimp [sheetPolynomial] at hroot
    push_cast
    linear_combination -hroot
  have hspeed : W * (a + Z) = (1 - (a : ℂ) * W) * (sheetCircleSpeed a W : ℂ) := by
    unfold sheetCircleSpeed
    push_cast
    rw [← mul_div_assoc]
    apply (eq_div_iff hdC).mpr
    calc
      _ = ((a : ℂ) + Z) * (W * (Complex.normSq (W - a) : ℂ)) := by ring
      _ = ((a : ℂ) + Z) * ((W - a) * (1 - (a : ℂ) * W)) := by rw [hprod]
      _ = (((a : ℂ) + Z) * (W - a)) * (1 - (a : ℂ) * W) := by ring
      _ = _ := by rw [hza]; push_cast; ring
  dsimp [sheetTorusDerivative]
  push_cast
  have hroot' : (a : ℂ) * Z - Z * W = -(1 - (a : ℂ) * W) := by
    dsimp [sheetPolynomial] at hroot
    linear_combination hroot
  rw [hroot']
  rw [show -(a : ℂ) * W - Z * W = -(W * ((a : ℂ) + Z)) by ring, hspeed]
  ring

/-- Every root has a derivative norm bounded below independently of its position. -/
theorem sheetTorusDerivative_norm_lower {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {Z W : ℂ} (hW : ‖W‖ = 1) (hroot : sheetPolynomial a Z W = 0) :
    1 - a ≤ ‖sheetTorusDerivative a Z W‖ := by
  have hbeta : 0 < beta := by linarith [beta_between_three_four]
  have hspeed := sheetCircleSpeed_pos ha ha1 hW
  have hden : 1 - a ≤ ‖(1 : ℂ) - a * W‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (a * W)
    simpa [norm_mul, hW, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] using h
  rw [sheetTorusDerivative_at_root ha ha1 hW hroot, norm_mul, norm_neg,
    ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 + beta * sheetCircleSpeed a W)]
  norm_num only [Complex.ofReal_one]
  exact hden.trans (le_mul_of_one_le_right (norm_nonneg _)
    (by nlinarith : 1 ≤ 1 + beta * sheetCircleSpeed a W))

theorem sheetTorusDerivative_ne_zero {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {Z W : ℂ} (hW : ‖W‖ = 1) (hroot : sheetPolynomial a Z W = 0) :
    sheetTorusDerivative a Z W ≠ 0 := by
  have h := sheetTorusDerivative_norm_lower ha ha1 hW hroot
  intro hz
  rw [hz, norm_zero] at h
  linarith

end

end MeyerGeneralProblem.StrongParity
