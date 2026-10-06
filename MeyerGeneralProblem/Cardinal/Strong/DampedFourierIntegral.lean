module

public import MeyerGeneralProblem.Cardinal.Strong.DampedTubeJump
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! The actual sum/integral interchange for the complete damped spectrum.
Its inverse Fourier action is the integrated literal quotient tube jump. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open Filter MeasureTheory
open scoped Topology FourierTransform

theorem schwartz_fourierInv_unitPhase_integral (f : SchwartzMap ℝ ℂ) (v : ℝ) :
    (𝓕⁻ f) v = ∫ x : ℝ, unitPhase (v * x) * f x := by
  change ((𝓕⁻ f : SchwartzMap ℝ ℂ) : ℝ → ℂ) v = _
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [RCLike.inner_apply, conj_trivial,
    unitPhase, smul_eq_mul]

/-- Actual integration of the full original damped spectral family. The unweighted
absolute convergence is proved from the actual tube expansions. -/
theorem productDampedSpectral_fourierInv_integral (s : ℕ)
    (r : productNumeratorIndex s → ℂ) {t : ℝ} (ht : 0 < t) (f : SchwartzMap ℝ ℂ) :
    (∑' y : spectralConeCarrier.subtype,
      dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient s r) t y *
        (𝓕⁻ f) y) = ∫ x : ℝ, productTubeJump s r t x * f x := by
  let b := dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient s r) t
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
    exact (productDampedSpectralCoefficient_norm_summable s r ht).mul_right _
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
      exact ((productDampedSpectral_hasSum_jump s r ht x).mul_right (f x)).tsum_eq

/-- The integrated ACTUAL quotient jump tends to the inverse Fourier action of the
complete original spectral record on every Schwartz test. -/
theorem productTubeJump_integral_tendsto_spectral (s : ℕ)
    (r : productNumeratorIndex s → ℂ) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, productTubeJump s r t x * f x)
      (𝓝[>] 0) (𝓝 ((𝓕⁻ (productSpectralDistribution s r)) f)) := by
  rw [TemperedDistribution.fourierInv_apply]
  apply (productDampedSpectral_sum_tendsto s r (𝓕⁻ f)).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact productDampedSpectral_fourierInv_integral s r ht f

end

end MeyerGeneralProblem.StrongParity
