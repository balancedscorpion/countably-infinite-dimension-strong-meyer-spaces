module

public import MeyerGeneralProblem.Cardinal.Strong.ContinuousRemainderJump
public import MeyerGeneralProblem.Cardinal.Strong.ProductPoleJump

@[expose] public section

/-! The actual quotient's integrated jump on a genuine neighborhood of
every complete original product root. All remainder hypotheses are discharged. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open Filter MeasureTheory
open scoped Topology FourierTransform

theorem productPoleRemainder_measurable (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : (productSheetCarrier s).subtype) : Measurable (productPoleRemainder s r x) := by
  have hf : Differentiable ℂ (complexSheetProduct s) :=
    fun z => (complexSheetProduct_hasDerivAt s z).differentiableAt
  exact simplePoleRemainder_measurable _ _ _ hf.continuous.measurable
    (complexProductSlabNumerator_differentiable s r).continuous.measurable

theorem productTubeJump_pole_remainder (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (a : (productSheetCarrier s).subtype) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    productTubeJump s r t x = realPoleJump (productPoleResidue s r a) a t x +
      (productPoleRemainder s r a ((x : ℂ) + (t : ℂ) * Complex.I) -
        productPoleRemainder s r a ((x : ℂ) - (t : ℂ) * Complex.I)) := by
  have hp : (x : ℂ) + (t : ℂ) * Complex.I ≠ (a : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add] at hi
    exact (ne_of_gt ht) hi
  have hn : (x : ℂ) - (t : ℂ) * Complex.I ≠ (a : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero] at hi
    exact (ne_of_gt ht) (by linarith)
  unfold productTubeJump
  rw [complexProductSlabQuotient_principal_part s r a hp,
    complexProductSlabQuotient_principal_part s r a hn]
  unfold realPoleJump
  push_cast
  ring

/-- Every actual original root has a positive test neighborhood on which the
integrated original quotient jump is exactly its original physical mass. -/
theorem productTubeJump_local_integral_tendsto (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (a : (productSheetCarrier s).subtype) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, f x ≠ 0 → |x - (a : ℝ)| ≤ δ) →
      Tendsto (fun t : ℝ => ∫ x : ℝ, productTubeJump s r t x * f x)
        (𝓝[>] 0) (𝓝 (productPhysicalResidue s r a * f a)) := by
  have hf : Differentiable ℂ (complexSheetProduct s) :=
    fun z => (complexSheetProduct_hasDerivAt s z).differentiableAt
  have hroot : complexSheetProduct s (a : ℂ) = 0 := by
    rw [complexSheetProduct_ofReal]
    exact a.property
  have ha : (a : ℂ) ∈ simplePoleRegularDomain (complexSheetProduct s) (a : ℂ) := by
    simpa only [simplePoleRegularDomain, Set.mem_ofPred_eq, dslope_same] using
      complexSheetProduct_deriv_ne_zero s hroot
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    ((simplePoleRegularDomain_isOpen _ _ hf).mem_nhds ha)
  refine ⟨ρ / 4, by positivity, ?_⟩
  intro f hsupport
  have hδ : 0 < ρ / 4 := by positivity
  have hclosed : Metric.closedBall (a : ℂ) (2 * (ρ / 4)) ⊆
      simplePoleRegularDomain (complexSheetProduct s) (a : ℂ) := by
    intro z hz
    apply hρsub
    apply Metric.mem_ball.mpr
    have hz' := Metric.mem_closedBall.mp hz
    linarith
  have hcont := (productPoleRemainder_continuousOn s r a).mono hclosed
  have hmeas := productPoleRemainder_measurable s r a
  have hrem := continuousRemainder_jump_integral_tendsto _ (a : ℝ) hδ hmeas hcont f hsupport
  have hlim := (productPoleJump_integral_tendsto s r a f).add hrem
  have heq : (fun t : ℝ =>
      (∫ x : ℝ, realPoleJump (productPoleResidue s r a) a t x * f x) +
        ∫ x : ℝ, (productPoleRemainder s r a ((x : ℂ) + (t : ℂ) * Complex.I) -
          productPoleRemainder s r a ((x : ℂ) - (t : ℂ) * Complex.I)) * f x) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => ∫ x : ℝ, productTubeJump s r t x * f x) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (eventually_lt_nhds hδ)] with t ht htd
    rw [← integral_add (realPoleJump_mul_integrable _ _ ht f.integrable)
      (continuousRemainder_jump_mul_integrable _ _ hmeas hcont ⟨ht, htd⟩ f hsupport)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [productTubeJump_pole_remainder s r a ht]
    ring
  simpa only [add_zero] using hlim.congr' heq

/-- Actual inverse Fourier action of the COMPLETE original spectral record at
each original root, on all tests in a genuine positive local neighborhood. -/
theorem productSpectral_fourierInv_local_root (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (a : (productSheetCarrier s).subtype) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, f x ≠ 0 → |x - (a : ℝ)| ≤ δ) →
      (𝓕⁻ (productSpectralDistribution s r)) f = productPhysicalResidue s r a * f a := by
  obtain ⟨δ, hδ, hlim⟩ := productTubeJump_local_integral_tendsto s r a
  refine ⟨δ, hδ, ?_⟩
  intro f hf
  exact tendsto_nhds_unique (productTubeJump_integral_tendsto_spectral s r f) (hlim f hf)

end

end MeyerGeneralProblem.StrongParity
