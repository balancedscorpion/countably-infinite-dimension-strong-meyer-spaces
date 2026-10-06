module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ReciprocalSlabSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralConeIndex
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.DampedSpectral
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.QuotientTubeSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPoleMass

@[expose] public section

/-! Original DampedSpectral for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open Filter
open scoped Topology

theorem productUpper_damped_norm_summable {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun p : ℕ × ℕ =>
      atomicExponentialDamping (positiveConeFrequency p) t *
        ‖productConeIndexCoefficient block r (.inl p)‖) := by
  have him : 0 < ((t : ℂ) * Complex.I).im := by simpa using ht
  have h := (productUpperTube_hasSum block r him).summable.norm
  convert! h using 1
  funext p
  rw [norm_mul, complexUnitPhase_vertical_norm]
  simp only [atomicExponentialDamping,
    abs_of_nonneg (positiveConeFrequency_nonneg p)]
  ring

theorem productLower_damped_norm_summable {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun p : ℕ × ℕ =>
      atomicExponentialDamping (positiveConeFrequency p) t *
        ‖-productSlabLowerCoefficient block r p.1 p.2 * unitPhase ((p.2 : ℝ) / 4)‖) := by
  have him : (((-t : ℝ) : ℂ) * Complex.I).im < 0 := by simpa using neg_neg_of_pos ht
  have h := (productLowerTube_hasSum block r him).summable.norm
  convert! h using 1
  funext p
  simp only [norm_mul]
  have he : -(positiveConeFrequency p : ℂ) * ((-t : ℝ) * Complex.I) =
      ((-positiveConeFrequency p : ℝ) : ℂ) * (((-t : ℝ) : ℂ) * Complex.I) := by
    push_cast
    rfl
  rw [he, complexUnitPhase_vertical_norm]
  simp only [atomicExponentialDamping,
    abs_of_nonneg (positiveConeFrequency_nonneg p)]
  simp only [neg_mul, mul_neg, neg_neg]
  ring

theorem dampedAtomicCoefficient_norm_at_label {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (t : ℝ) (p : spectralConeIndex) :
    ‖dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient block r) t
      (spectralConeIndexPoint p)‖ =
      atomicExponentialDamping (spectralConeIndexFrequency p) t *
        ‖productConeIndexCoefficient block r p‖ := by
  unfold dampedAtomicCoefficient
  rw [norm_mul, atomicExponentialDamping_norm, productSpectralCoefficient_at_label]
  rfl

/-- Actual unweighted absolute convergence after every strictly positive damping. -/
theorem productDampedSpectralCoefficient_norm_summable {s : ℕ} (block : CompactOriginalParameterBlock s)
    (r : productNumeratorIndex s → ℂ) {t : ℝ} (ht : 0 < t) :
    Summable (fun x : spectralConeCarrier.subtype =>
      ‖dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient block r) t x‖) := by
  apply spectralConeEquiv.summable_iff.mp
  apply Summable.sum
  · change Summable (fun p : ℕ × ℕ =>
      ‖dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient block r) t
        (spectralConeIndexPoint (.inl p))‖)
    convert! productUpper_damped_norm_summable block r ht using 1
    funext p
    exact dampedAtomicCoefficient_norm_at_label block r t (.inl p)
  · change Summable (fun p : {p : ℕ × ℕ // p ≠ (0, 0)} =>
      ‖dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient block r) t
        (spectralConeIndexPoint (.inr p))‖)
    have h := (productLower_damped_norm_summable block r ht).comp_injective
      (Subtype.val_injective (p := fun p : ℕ × ℕ => p ≠ (0, 0)))
    convert! h using 1
    funext p
    convert! dampedAtomicCoefficient_norm_at_label block r t (.inr p) using 1
    simp only [Function.comp_def, productConeIndexCoefficient, spectralConeIndexFrequency,
      atomicExponentialDamping, abs_neg]

/-- Removing literal damping recovers the actual complete original spectral record. -/
theorem productDampedSpectral_sum_tendsto {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun t : ℝ => ∑' x : spectralConeCarrier.subtype,
      dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient block r) t x * f x)
      (𝓝[>] 0) (𝓝 (productSpectralDistribution block r f)) :=
  dampedAtomic_sum_tendsto spectralConeCarrier (productSpectralCoefficient block r) (s + 3)
    (productSpectralCoefficient_weight_summable block r) f

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
