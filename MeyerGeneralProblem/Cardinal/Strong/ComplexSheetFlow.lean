module

public import MeyerGeneralProblem.Cardinal.Strong.SheetFlow

@[expose] public section

/-!
# Literal complex sheets have only real roots

The Blaschke norm-square identity excludes a zero when both exponential
phases lie strictly inside, or strictly outside, the unit circle. The
complex extension agrees exactly with the original real quarter flow.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The entire extension of the original period-one phase. -/
def complexUnitPhase (z : ℂ) : ℂ := Complex.exp ((2 * Real.pi : ℝ) * Complex.I * z)

/-- The literal sheet polynomial on the complex quarter-phase flow. -/
def complexSheetFlow (a : ℝ) (z : ℂ) : ℂ :=
  sheetPolynomial a (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4))

theorem complexUnitPhase_ofReal (x : ℝ) : complexUnitPhase x = unitPhase x := by
  unfold complexUnitPhase unitPhase
  congr 1
  push_cast
  ring

theorem complexSheetFlow_ofReal (a x : ℝ) : complexSheetFlow a x = sheetFlow a x := by
  unfold complexSheetFlow sheetFlow
  rw [complexUnitPhase_ofReal]
  rw [show (beta : ℂ) * (x : ℂ) - 1 / 4 = (beta * x - 1 / 4 : ℝ) by push_cast; ring,
    complexUnitPhase_ofReal]

theorem complexUnitPhase_norm (z : ℂ) :
    ‖complexUnitPhase z‖ = Real.exp (-2 * Real.pi * z.im) := by
  rw [complexUnitPhase, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- The disk/exterior comparison is an exact polynomial identity. -/
theorem blaschke_normSq_difference (a : ℝ) (W : ℂ) :
    Complex.normSq (W - a) - Complex.normSq (1 - a * W) =
      (1 - a ^ 2) * (Complex.normSq W - 1) := by
  rw [Complex.normSq_sub, Complex.normSq_sub, Complex.normSq_mul]
  simp only [Complex.normSq_ofReal, Complex.normSq_one, map_mul, Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, Complex.conj_re, Complex.conj_im]
  ring

theorem sheet_root_normSq {a : ℝ} {Z W : ℂ} (hroot : sheetPolynomial a Z W = 0) :
    Complex.normSq Z * Complex.normSq (W - a) = Complex.normSq (1 - a * W) := by
  have hid : Z * (W - a) = 1 - a * W := by
    dsimp [sheetPolynomial] at hroot
    linear_combination -hroot
  rw [← Complex.normSq_mul, hid]

theorem sheetPolynomial_ne_zero_inside {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {Z W : ℂ} (hZ : ‖Z‖ ≤ 1) (hW : ‖W‖ < 1) : sheetPolynomial a Z W ≠ 0 := by
  intro hroot
  have hz : Complex.normSq Z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg Z]
  have hw : Complex.normSq W < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg W]
  have hfactor : 0 < 1 - a ^ 2 := by nlinarith
  have hdiff := blaschke_normSq_difference a W
  have heq := sheet_root_normSq hroot
  nlinarith [Complex.normSq_nonneg (W - a)]

theorem sheetPolynomial_ne_zero_outside {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {Z W : ℂ} (hZ : 1 ≤ ‖Z‖) (hW : 1 < ‖W‖) : sheetPolynomial a Z W ≠ 0 := by
  intro hroot
  have hz : 1 ≤ Complex.normSq Z := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg Z]
  have hw : 1 < Complex.normSq W := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg W]
  have hfactor : 0 < 1 - a ^ 2 := by nlinarith
  have hdiff := blaschke_normSq_difference a W
  have heq := sheet_root_normSq hroot
  nlinarith [Complex.normSq_nonneg (W - a)]

/-- All complex zeros of the actual sheet have zero imaginary part. -/
theorem complexSheetFlow_root_real {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {z : ℂ} (hroot : complexSheetFlow a z = 0) : z.im = 0 := by
  have hbeta : 0 < beta := by linarith [beta_between_three_four]
  have hWnorm : ‖complexUnitPhase (beta * z - 1 / 4)‖ =
      Real.exp (-2 * Real.pi * beta * z.im) := by
    rw [complexUnitPhase_norm]
    congr 1
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im, Complex.one_im]
    ring
  rcases lt_trichotomy z.im 0 with hz | hz | hz
  · have hZ : 1 < ‖complexUnitPhase z‖ := by
      rw [complexUnitPhase_norm, Real.one_lt_exp_iff]
      nlinarith [Real.pi_pos]
    have hW : 1 < ‖complexUnitPhase (beta * z - 1 / 4)‖ := by
      rw [hWnorm, Real.one_lt_exp_iff]
      nlinarith [mul_pos Real.pi_pos (mul_pos hbeta (neg_pos.mpr hz))]
    exact False.elim (sheetPolynomial_ne_zero_outside ha ha1 hZ.le hW hroot)
  · exact hz
  · have hZ : ‖complexUnitPhase z‖ < 1 := by
      rw [complexUnitPhase_norm, Real.exp_lt_one_iff]
      nlinarith [Real.pi_pos]
    have hW : ‖complexUnitPhase (beta * z - 1 / 4)‖ < 1 := by
      rw [hWnorm, Real.exp_lt_one_iff]
      nlinarith [mul_pos Real.pi_pos (mul_pos hbeta hz)]
    exact False.elim (sheetPolynomial_ne_zero_inside ha ha1 hZ.le hW hroot)

theorem complexUnitPhase_hasDerivAt (z : ℂ) :
    HasDerivAt complexUnitPhase ((2 * Real.pi : ℝ) * Complex.I * complexUnitPhase z) z := by
  change HasDerivAt (fun w : ℂ => Complex.exp ((2 * Real.pi : ℝ) * Complex.I * w)) _ z
  have h := ((hasDerivAt_id z).const_mul ((2 * Real.pi : ℝ) * Complex.I)).cexp
  simpa [complexUnitPhase, id_eq, mul_comm, mul_assoc, mul_left_comm] using h

/-- The entire sheet derivative is the same literal torus-direction expression. -/
theorem complexSheetFlow_hasDerivAt (a : ℝ) (z : ℂ) :
    HasDerivAt (complexSheetFlow a) ((2 * Real.pi : ℝ) * Complex.I *
      sheetTorusDerivative a (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4))) z := by
  have hZ := complexUnitPhase_hasDerivAt z
  have hinner : HasDerivAt (fun w : ℂ => beta * w - 1 / 4) (beta : ℂ) z := by
    simpa using (((hasDerivAt_id z).const_mul (beta : ℂ)).sub_const (1 / 4))
  have hW := (complexUnitPhase_hasDerivAt (beta * z - 1 / 4)).comp z hinner
  have h := (((hasDerivAt_const z (1 : ℂ)).sub (hW.const_mul (a : ℂ))).add
    (hZ.const_mul (a : ℂ))).sub (hZ.mul hW)
  convert! h using 1
  simp only [sheetTorusDerivative, Function.comp_apply]
  push_cast
  ring

/-- Every complex root is simple, using reality and the actual real derivative. -/
theorem complexSheetFlow_deriv_ne_zero {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {z : ℂ} (hroot : complexSheetFlow a z = 0) : deriv (complexSheetFlow a) z ≠ 0 := by
  have hz : z = (z.re : ℂ) := by
    apply Complex.ext_iff.mpr
    constructor
    · simp only [Complex.ofReal_re]
    · simpa only [Complex.ofReal_im] using complexSheetFlow_root_real ha ha1 hroot
  have hrootR : sheetFlow a z.re = 0 := by
    rw [← complexSheetFlow_ofReal, ← hz]
    exact hroot
  have hf := complexSheetFlow_hasDerivAt a (z.re : ℂ)
  have hR := hf.comp_ofReal
  have hfun : (fun x : ℝ => complexSheetFlow a x) = sheetFlow a := by
    funext x
    exact complexSheetFlow_ofReal a x
  rw [hfun] at hR
  have heq : deriv (complexSheetFlow a) (z.re : ℂ) = deriv (sheetFlow a) z.re :=
    hf.deriv.trans hR.deriv.symm
  rw [hz, heq]
  exact sheetFlow_deriv_ne_zero ha ha1 hrootR

end

end MeyerGeneralProblem.StrongParity
