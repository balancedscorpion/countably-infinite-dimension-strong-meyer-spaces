module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPoleMass
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.QuotientTubeSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ReciprocalSlabSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralConeIndex
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.DampedTubeJump
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.DampedSpectral

@[expose] public section

/-! Original DampedTubeJump for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The actual upper-minus-lower values of the complete original quotient. -/
def productTubeJump {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) (t x : ℝ) : ℂ :=
  complexProductSlabQuotient block r ((x : ℂ) + (t : ℂ) * Complex.I) -
    complexProductSlabQuotient block r ((x : ℂ) - (t : ℂ) * Complex.I)

theorem productDampedConeIndex_hasSum {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun p : spectralConeIndex =>
      (atomicExponentialDamping (spectralConeIndexFrequency p) t : ℂ) *
        productConeIndexCoefficient block r p * unitPhase (spectralConeIndexFrequency p * x))
      (productTubeJump block r t x) := by
  have hplus : 0 < ((x : ℂ) + (t : ℂ) * Complex.I).im := by simpa using ht
  have hminus : ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I).im < 0 := by
    simpa using neg_neg_of_pos ht
  have hu := productUpperTube_hasSum block r hplus
  have hl := productLowerTube_hasSum block r hminus
  let fn : ℕ × ℕ → ℂ := fun p =>
    (atomicExponentialDamping (-positiveConeFrequency p) t : ℂ) *
      (-productSlabLowerCoefficient block r p.1 p.2 * unitPhase ((p.2 : ℝ) / 4)) *
        unitPhase (-positiveConeFrequency p * x)
  have hfull : HasSum fn
      (-complexProductSlabQuotient block r ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) := by
    apply hl.congr_fun
    intro p
    rw [complexUnitPhase_damped_lower (positiveConeFrequency_nonneg p)]
    dsimp [fn]
    ring
  have hsupp : Function.support fn ⊆ {p : ℕ × ℕ | p ≠ (0, 0)} := by
    intro p hp hzero
    change p = (0, 0) at hzero
    subst p
    exact hp (by simp only [fn, productSlabLowerCoefficient_zero_zero, neg_zero,
      zero_mul, mul_zero])
  have hn := (hasSum_subtype_iff_of_support_subset hsupp).mpr hfull
  have hsum : HasSum (fun p : spectralConeIndex =>
      (atomicExponentialDamping (spectralConeIndexFrequency p) t : ℂ) *
        productConeIndexCoefficient block r p * unitPhase (spectralConeIndexFrequency p * x))
      (complexProductSlabQuotient block r ((x : ℂ) + (t : ℂ) * Complex.I) +
        -complexProductSlabQuotient block r ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) := by
    apply HasSum.sum
    · apply hu.congr_fun
      intro p
      rw [complexUnitPhase_damped_upper (positiveConeFrequency_nonneg p)]
      change (atomicExponentialDamping (positiveConeFrequency p) t : ℂ) *
        productConeIndexCoefficient block r (.inl p) * unitPhase (positiveConeFrequency p * x) = _
      ring
    · convert! hn using 1
  convert! hsum using 1
  unfold productTubeJump
  rw [show (x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
    (x : ℂ) - (t : ℂ) * Complex.I by push_cast; ring]
  rfl

/-- The complete actual coarse carrier series, without duplicating zero, equals the
actual quotient jump for every positive tube height. -/
theorem productDampedSpectral_hasSum_jump {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun y : spectralConeCarrier.subtype =>
      dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient block r) t y *
        unitPhase ((y : ℝ) * x)) (productTubeJump block r t x) := by
  apply spectralConeEquiv.hasSum_iff.mp
  convert! productDampedConeIndex_hasSum block r ht x using 1
  funext p
  change (atomicExponentialDamping (spectralConeIndexFrequency p) t : ℂ) *
    productSpectralCoefficient block r (spectralConeIndexPoint p) *
      unitPhase (spectralConeIndexFrequency p * x) = _
  rw [productSpectralCoefficient_at_label]

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
