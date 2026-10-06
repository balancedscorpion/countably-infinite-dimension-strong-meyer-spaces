module

public import MeyerGeneralProblem.Cardinal.Strong.SpectralDistribution

@[expose] public section

/-! Literal upper and lower half-plane evaluations of the original quotient.
These are genuine analytic series identities, before the Fourier boundary jump. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem complexUnitPhase_inv (z : ℂ) : (complexUnitPhase z)⁻¹ = complexUnitPhase (-z) := by
  unfold complexUnitPhase
  rw [← Complex.exp_neg]
  congr 1
  ring

theorem complexUnitPhase_norm_lt_one {z : ℂ} (hz : 0 < z.im) : ‖complexUnitPhase z‖ < 1 := by
  rw [complexUnitPhase_norm, Real.exp_lt_one_iff]
  nlinarith [Real.pi_pos]

theorem complexUnitPhase_inv_norm_lt_one {z : ℂ} (hz : z.im < 0) :
    ‖(complexUnitPhase z)⁻¹‖ < 1 := by
  rw [complexUnitPhase_inv]
  exact complexUnitPhase_norm_lt_one (by simpa only [Complex.neg_im] using neg_pos.mpr hz)

theorem quarterFlow_phase_power (p : ℕ × ℕ) (z : ℂ) :
    complexUnitPhase z ^ p.1 * complexUnitPhase (beta * z - 1 / 4) ^ p.2 =
      unitPhase (-(p.2 : ℝ) / 4) * complexUnitPhase ((positiveConeFrequency p : ℂ) * z) := by
  unfold complexUnitPhase unitPhase positiveConeFrequency
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem quarterFlow_inverse_phase_power (p : ℕ × ℕ) (z : ℂ) :
    (complexUnitPhase z)⁻¹ ^ p.1 * (complexUnitPhase (beta * z - 1 / 4))⁻¹ ^ p.2 =
      unitPhase ((p.2 : ℝ) / 4) * complexUnitPhase (-(positiveConeFrequency p : ℂ) * z) := by
  rw [complexUnitPhase_inv, complexUnitPhase_inv]
  unfold complexUnitPhase unitPhase positiveConeFrequency
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The original full upper cone series equals the original quotient on the upper half-plane. -/
theorem productUpperTube_hasSum (s : ℕ) (r : productNumeratorIndex s → ℂ)
    {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun p : ℕ × ℕ => productConeIndexCoefficient s r (.inl p) *
      complexUnitPhase ((positiveConeFrequency p : ℂ) * z))
      (productSlabPolynomial s r (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4)) /
        productSheetPolynomial s (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4))) := by
  have hb : 0 < beta := lt_trans (by norm_num) beta_between_three_four.1
  have hW : 0 < ((beta : ℂ) * z - 1 / 4).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im, Complex.one_im, zero_mul, add_zero, zero_div, sub_zero]
    exact mul_pos hb hz
  have h := productSlabUpperCoefficient_hasSum s r
    (complexUnitPhase_norm_lt_one hz) (complexUnitPhase_norm_lt_one hW)
  apply h.congr_fun
  intro p
  unfold productConeIndexCoefficient
  rw [mul_assoc, ← quarterFlow_phase_power, ← mul_assoc]

/-- The original lower jump series equals minus the original quotient on the lower half-plane. -/
theorem productLowerTube_hasSum (s : ℕ) (r : productNumeratorIndex s → ℂ)
    {z : ℂ} (hz : z.im < 0) :
    HasSum (fun p : ℕ × ℕ =>
      (-productSlabLowerCoefficient s r p.1 p.2 * unitPhase ((p.2 : ℝ) / 4)) *
        complexUnitPhase (-(positiveConeFrequency p : ℂ) * z))
      (-(productSlabPolynomial s r (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4)) /
        productSheetPolynomial s (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4)))) := by
  have hb : 0 < beta := lt_trans (by norm_num) beta_between_three_four.1
  have hW : ((beta : ℂ) * z - 1 / 4).im < 0 := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im, Complex.one_im, zero_mul, add_zero, zero_div, sub_zero]
    exact mul_neg_of_pos_of_neg hb hz
  have h := (productSlabLowerCoefficient_exterior_hasSum s r
    (Z := complexUnitPhase z) (W := complexUnitPhase (beta * z - 1 / 4))
    (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    (complexUnitPhase_inv_norm_lt_one hz) (complexUnitPhase_inv_norm_lt_one hW)).neg
  apply h.congr_fun
  intro p
  rw [mul_assoc, ← quarterFlow_inverse_phase_power]
  ring

end

end MeyerGeneralProblem.StrongParity
