module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.DampedTubeJump
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPoleMass
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductResidues
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.LocalProductJump
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPoleJump
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.DampedFourierIntegral

@[expose] public section

/-! Original LocalProductJump for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open Filter MeasureTheory
open scoped Topology FourierTransform

theorem productPoleRemainder_measurable {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : (compactOriginalProductSheetCarrier block).subtype) : Measurable (productPoleRemainder block r x) := by
  have hf : Differentiable ℂ (compactOriginalComplexSheetProduct block) :=
    fun z => (compactOriginalComplexSheetProduct_hasDerivAt block z).differentiableAt
  exact simplePoleRemainder_measurable _ _ _ hf.continuous.measurable
    (complexProductSlabNumerator_differentiable s r).continuous.measurable

theorem productTubeJump_pole_remainder {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (a : (compactOriginalProductSheetCarrier block).subtype) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    productTubeJump block r t x = realPoleJump (productPoleResidue block r a) a t x +
      (productPoleRemainder block r a ((x : ℂ) + (t : ℂ) * Complex.I) -
        productPoleRemainder block r a ((x : ℂ) - (t : ℂ) * Complex.I)) := by
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
  rw [complexProductSlabQuotient_principal_part block r a hp,
    complexProductSlabQuotient_principal_part block r a hn]
  unfold realPoleJump
  push_cast
  ring

/-- Every actual original root has a positive test neighborhood on which the
integrated original quotient jump is exactly its original physical mass. -/
theorem productTubeJump_local_integral_tendsto {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (a : (compactOriginalProductSheetCarrier block).subtype) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, f x ≠ 0 → |x - (a : ℝ)| ≤ δ) →
      Tendsto (fun t : ℝ => ∫ x : ℝ, productTubeJump block r t x * f x)
        (𝓝[>] 0) (𝓝 (productPhysicalResidue block r a * f a)) := by
  have hf : Differentiable ℂ (compactOriginalComplexSheetProduct block) :=
    fun z => (compactOriginalComplexSheetProduct_hasDerivAt block z).differentiableAt
  have hroot : compactOriginalComplexSheetProduct block (a : ℂ) = 0 := by
    rw [compactOriginalComplexSheetProduct_ofReal block]
    exact a.property
  have ha : (a : ℂ) ∈ simplePoleRegularDomain (compactOriginalComplexSheetProduct block) (a : ℂ) := by
    simpa only [simplePoleRegularDomain, Set.mem_ofPred_eq, dslope_same] using
      compactOriginalComplexSheetProduct_deriv_ne_zero block hroot
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    ((simplePoleRegularDomain_isOpen _ _ hf).mem_nhds ha)
  refine ⟨ρ / 4, by positivity, ?_⟩
  intro f hsupport
  have hδ : 0 < ρ / 4 := by positivity
  have hclosed : Metric.closedBall (a : ℂ) (2 * (ρ / 4)) ⊆
      simplePoleRegularDomain (compactOriginalComplexSheetProduct block) (a : ℂ) := by
    intro z hz
    apply hρsub
    apply Metric.mem_ball.mpr
    have hz' := Metric.mem_closedBall.mp hz
    linarith
  have hcont := (productPoleRemainder_continuousOn block r a).mono hclosed
  have hmeas := productPoleRemainder_measurable block r a
  have hrem := continuousRemainder_jump_integral_tendsto _ (a : ℝ) hδ hmeas hcont f hsupport
  have hlim := (productPoleJump_integral_tendsto block r a f).add hrem
  have heq : (fun t : ℝ =>
      (∫ x : ℝ, realPoleJump (productPoleResidue block r a) a t x * f x) +
        ∫ x : ℝ, (productPoleRemainder block r a ((x : ℂ) + (t : ℂ) * Complex.I) -
          productPoleRemainder block r a ((x : ℂ) - (t : ℂ) * Complex.I)) * f x) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => ∫ x : ℝ, productTubeJump block r t x * f x) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (eventually_lt_nhds hδ)] with t ht htd
    rw [← integral_add (realPoleJump_mul_integrable _ _ ht f.integrable)
      (continuousRemainder_jump_mul_integrable _ _ hmeas hcont ⟨ht, htd⟩ f hsupport)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [productTubeJump_pole_remainder block r a ht]
    ring
  simpa only [add_zero] using hlim.congr' heq

/-- Actual inverse Fourier action of the COMPLETE original spectral record at
each original root, on all tests in a genuine positive local neighborhood. -/
theorem productSpectral_fourierInv_local_root {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (a : (compactOriginalProductSheetCarrier block).subtype) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, f x ≠ 0 → |x - (a : ℝ)| ≤ δ) →
      (𝓕⁻ (productSpectralDistribution block r)) f = productPhysicalResidue block r a * f a := by
  obtain ⟨δ, hδ, hlim⟩ := productTubeJump_local_integral_tendsto block r a
  refine ⟨δ, hδ, ?_⟩
  intro f hf
  exact tendsto_nhds_unique (productTubeJump_integral_tendsto_spectral block r f) (hlim f hf)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
