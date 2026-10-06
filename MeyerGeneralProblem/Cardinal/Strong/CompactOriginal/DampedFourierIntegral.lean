module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.DampedSpectral
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralConeIndex
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.DampedFourierIntegral
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.DampedTubeJump

@[expose] public section

/-! Original DampedFourierIntegral for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open Filter MeasureTheory
open scoped Topology FourierTransform

/-- Actual integration of the full original damped spectral family. The unweighted
absolute convergence is proved from the actual tube expansions. -/
theorem productDampedSpectral_fourierInv_integral {s : ℕ} (block : CompactOriginalParameterBlock s)
    (r : productNumeratorIndex s → ℂ) {t : ℝ} (ht : 0 < t) (f : SchwartzMap ℝ ℂ) :
    (∑' y : spectralConeCarrier.subtype,
      dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient block r) t y *
        (𝓕⁻ f) y) = ∫ x : ℝ, productTubeJump block r t x * f x := by
  let b := dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient block r) t
  let F : spectralConeCarrier.subtype → ℝ → ℂ :=
    fun y x => b y * unitPhase ((y : ℝ) * x) * f x
  have hi (y : spectralConeCarrier.subtype) : Integrable (F y) := by
    have hc : Continuous (fun x : ℝ => b y * unitPhase ((y : ℝ) * x)) := by
      unfold unitPhase
      fun_prop
    apply f.integrable.bdd_mul (c := ‖b y‖) hc.aestronglyMeasurable
    filter_upwards [] with x
    simp only [norm_mul, unitPhase_norm, mul_one, le_refl]
  have hnorm (y : spectralConeCarrier.subtype) :
      (∫ x : ℝ, ‖F y x‖) = ‖b y‖ * ∫ x : ℝ, ‖f x‖ := by
    simp only [F, norm_mul, unitPhase_norm, mul_one]
    exact integral_const_mul _ _
  have hs : Summable (fun y : spectralConeCarrier.subtype => ∫ x : ℝ, ‖F y x‖) := by
    simp_rw [hnorm]
    exact (productDampedSpectralCoefficient_norm_summable block r ht).mul_right _
  have hswap := hasSum_integral_of_summable_integral_norm hi hs
  calc
    _ = ∑' y : spectralConeCarrier.subtype, ∫ x : ℝ, F y x := by
      apply tsum_congr
      intro y
      rw [schwartz_fourierInv_unitPhase_integral, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [F, b]
      ring
    _ = ∫ x : ℝ, ∑' y : spectralConeCarrier.subtype, F y x := hswap.tsum_eq
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact ((productDampedSpectral_hasSum_jump block r ht x).mul_right (f x)).tsum_eq

/-- The integrated ACTUAL quotient jump tends to the inverse Fourier action of the
complete original spectral record on every Schwartz test. -/
theorem productTubeJump_integral_tendsto_spectral {s : ℕ} (block : CompactOriginalParameterBlock s)
    (r : productNumeratorIndex s → ℂ) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, productTubeJump block r t x * f x)
      (𝓝[>] 0) (𝓝 ((𝓕⁻ (productSpectralDistribution block r)) f)) := by
  rw [TemperedDistribution.fourierInv_apply]
  apply (productDampedSpectral_sum_tendsto block r (𝓕⁻ f)).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact productDampedSpectral_fourierInv_integral block r ht f

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
