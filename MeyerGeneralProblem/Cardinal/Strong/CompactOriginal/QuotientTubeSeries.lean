module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.LowerQuotientSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ReciprocalSlabSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SlabPowerSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralConeIndex
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.QuotientTubeSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralDistribution

@[expose] public section

/-! Original QuotientTubeSeries for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The original full upper cone series equals the original quotient on the upper half-plane. -/
theorem productUpperTube_hasSum {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun p : ℕ × ℕ => productConeIndexCoefficient block r (.inl p) *
      complexUnitPhase ((positiveConeFrequency p : ℂ) * z))
      (productSlabPolynomial s r (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4)) /
        compactOriginalSheetPolynomial block (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4))) := by
  have hb : 0 < beta := lt_trans (by norm_num) beta_between_three_four.1
  have hW : 0 < ((beta : ℂ) * z - 1 / 4).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im, Complex.one_im, zero_mul, add_zero, zero_div, sub_zero]
    exact mul_pos hb hz
  have h := productSlabUpperCoefficient_hasSum block r
    (complexUnitPhase_norm_lt_one hz) (complexUnitPhase_norm_lt_one hW)
  apply h.congr_fun
  intro p
  unfold productConeIndexCoefficient
  rw [mul_assoc, ← quarterFlow_phase_power, ← mul_assoc]

/-- The original lower jump series equals minus the original quotient on the lower half-plane. -/
theorem productLowerTube_hasSum {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    {z : ℂ} (hz : z.im < 0) :
    HasSum (fun p : ℕ × ℕ =>
      (-productSlabLowerCoefficient block r p.1 p.2 * unitPhase ((p.2 : ℝ) / 4)) *
        complexUnitPhase (-(positiveConeFrequency p : ℂ) * z))
      (-(productSlabPolynomial s r (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4)) /
        compactOriginalSheetPolynomial block (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4)))) := by
  have hb : 0 < beta := lt_trans (by norm_num) beta_between_three_four.1
  have hW : ((beta : ℂ) * z - 1 / 4).im < 0 := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_im, Complex.one_im, zero_mul, add_zero, zero_div, sub_zero]
    exact mul_neg_of_pos_of_neg hb hz
  have h := (productSlabLowerCoefficient_exterior_hasSum block r
    (Z := complexUnitPhase z) (W := complexUnitPhase (beta * z - 1 / 4))
    (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    (complexUnitPhase_inv_norm_lt_one hz) (complexUnitPhase_inv_norm_lt_one hW)).neg
  apply h.congr_fun
  intro p
  rw [mul_assoc, ← quarterFlow_inverse_phase_power]
  ring

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
