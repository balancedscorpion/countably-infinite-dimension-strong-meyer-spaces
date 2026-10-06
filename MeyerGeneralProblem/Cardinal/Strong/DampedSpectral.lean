module

public import MeyerGeneralProblem.Cardinal.Strong.QuotientTubeSeries
public import MeyerGeneralProblem.Cardinal.Strong.ProductPoleMass
public import MeyerGeneralProblem.Distribution.DampedAtomic

@[expose] public section

/-! Absolute summability of the actual damped original spectrum and its
weak boundary limit on the complete original coarse cone. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open Filter
open scoped Topology

theorem complexUnitPhase_vertical_norm (v t : ℝ) :
    ‖complexUnitPhase ((v : ℂ) * ((t : ℂ) * Complex.I))‖ =
      Real.exp (-2 * Real.pi * v * t) := by
  rw [complexUnitPhase_norm]
  congr 1
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem productUpper_damped_norm_summable (s : ℕ) (r : productNumeratorIndex s → ℂ)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun p : ℕ × ℕ =>
      atomicExponentialDamping (positiveConeFrequency p) t *
        ‖productConeIndexCoefficient s r (.inl p)‖) := by
  have him : 0 < ((t : ℂ) * Complex.I).im := by simpa using ht
  have h := (productUpperTube_hasSum s r him).summable.norm
  convert! h using 1
  funext p
  rw [norm_mul, complexUnitPhase_vertical_norm]
  simp only [atomicExponentialDamping,
    abs_of_nonneg (positiveConeFrequency_nonneg p)]
  ring

theorem productLower_damped_norm_summable (s : ℕ) (r : productNumeratorIndex s → ℂ)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun p : ℕ × ℕ =>
      atomicExponentialDamping (positiveConeFrequency p) t *
        ‖-productSlabLowerCoefficient s r p.1 p.2 * unitPhase ((p.2 : ℝ) / 4)‖) := by
  have him : (((-t : ℝ) : ℂ) * Complex.I).im < 0 := by simpa using neg_neg_of_pos ht
  have h := (productLowerTube_hasSum s r him).summable.norm
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

theorem dampedAtomicCoefficient_norm_at_label (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (t : ℝ) (p : spectralConeIndex) :
    ‖dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient s r) t
      (spectralConeIndexPoint p)‖ =
      atomicExponentialDamping (spectralConeIndexFrequency p) t *
        ‖productConeIndexCoefficient s r p‖ := by
  unfold dampedAtomicCoefficient
  rw [norm_mul, atomicExponentialDamping_norm, productSpectralCoefficient_at_label]
  rfl

/-- Actual unweighted absolute convergence after every strictly positive damping. -/
theorem productDampedSpectralCoefficient_norm_summable (s : ℕ)
    (r : productNumeratorIndex s → ℂ) {t : ℝ} (ht : 0 < t) :
    Summable (fun x : spectralConeCarrier.subtype =>
      ‖dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient s r) t x‖) := by
  apply spectralConeEquiv.summable_iff.mp
  apply Summable.sum
  · change Summable (fun p : ℕ × ℕ =>
      ‖dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient s r) t
        (spectralConeIndexPoint (.inl p))‖)
    convert! productUpper_damped_norm_summable s r ht using 1
    funext p
    exact dampedAtomicCoefficient_norm_at_label s r t (.inl p)
  · change Summable (fun p : {p : ℕ × ℕ // p ≠ (0, 0)} =>
      ‖dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient s r) t
        (spectralConeIndexPoint (.inr p))‖)
    have h := (productLower_damped_norm_summable s r ht).comp_injective
      (Subtype.val_injective (p := fun p : ℕ × ℕ => p ≠ (0, 0)))
    convert! h using 1
    funext p
    convert! dampedAtomicCoefficient_norm_at_label s r t (.inr p) using 1
    simp only [Function.comp_def, productConeIndexCoefficient, spectralConeIndexFrequency,
      atomicExponentialDamping, abs_neg]

/-- Removing literal damping recovers the actual complete original spectral record. -/
theorem productDampedSpectral_sum_tendsto (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun t : ℝ => ∑' x : spectralConeCarrier.subtype,
      dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient s r) t x * f x)
      (𝓝[>] 0) (𝓝 (productSpectralDistribution s r f)) :=
  dampedAtomic_sum_tendsto spectralConeCarrier (productSpectralCoefficient s r) (s + 3)
    (productSpectralCoefficient_weight_summable s r) f

end

end MeyerGeneralProblem.StrongParity
