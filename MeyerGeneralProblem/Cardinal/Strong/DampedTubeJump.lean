module

public import MeyerGeneralProblem.Cardinal.Strong.DampedSpectral

@[expose] public section

/-! The literal damped spectral series is the original meromorphic tube
jump. Both signs and the single zero-frequency term are retained. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem complexUnitPhase_horizontal_vertical (v x t : ℝ) :
    complexUnitPhase ((v : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)) =
      (Real.exp (-2 * Real.pi * v * t) : ℂ) * unitPhase (v * x) := by
  unfold complexUnitPhase unitPhase
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  norm_num [Complex.I_sq]
  ring

theorem complexUnitPhase_damped_upper {v : ℝ} (hv : 0 ≤ v) (x t : ℝ) :
    complexUnitPhase ((v : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)) =
      (atomicExponentialDamping v t : ℂ) * unitPhase (v * x) := by
  rw [complexUnitPhase_horizontal_vertical]
  simp only [atomicExponentialDamping, abs_of_nonneg hv]

theorem complexUnitPhase_damped_lower {v : ℝ} (hv : 0 ≤ v) (x t : ℝ) :
    complexUnitPhase (-(v : ℂ) * ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) =
      (atomicExponentialDamping (-v) t : ℂ) * unitPhase ((-v) * x) := by
  rw [show -(v : ℂ) = ((-v : ℝ) : ℂ) by simp only [Complex.ofReal_neg],
    complexUnitPhase_horizontal_vertical]
  simp only [atomicExponentialDamping, abs_neg, abs_of_nonneg hv,
    neg_mul, mul_neg, neg_neg]

/-- The actual upper-minus-lower values of the complete original quotient. -/
def productTubeJump (s : ℕ) (r : productNumeratorIndex s → ℂ) (t x : ℝ) : ℂ :=
  complexProductSlabQuotient s r ((x : ℂ) + (t : ℂ) * Complex.I) -
    complexProductSlabQuotient s r ((x : ℂ) - (t : ℂ) * Complex.I)

theorem productDampedConeIndex_hasSum (s : ℕ) (r : productNumeratorIndex s → ℂ)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun p : spectralConeIndex =>
      (atomicExponentialDamping (spectralConeIndexFrequency p) t : ℂ) *
        productConeIndexCoefficient s r p * unitPhase (spectralConeIndexFrequency p * x))
      (productTubeJump s r t x) := by
  have hplus : 0 < ((x : ℂ) + (t : ℂ) * Complex.I).im := by simpa using ht
  have hminus : ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I).im < 0 := by
    simpa using neg_neg_of_pos ht
  have hu := productUpperTube_hasSum s r hplus
  have hl := productLowerTube_hasSum s r hminus
  let fn : ℕ × ℕ → ℂ := fun p =>
    (atomicExponentialDamping (-positiveConeFrequency p) t : ℂ) *
      (-productSlabLowerCoefficient s r p.1 p.2 * unitPhase ((p.2 : ℝ) / 4)) *
        unitPhase (-positiveConeFrequency p * x)
  have hfull : HasSum fn
      (-complexProductSlabQuotient s r ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) := by
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
        productConeIndexCoefficient s r p * unitPhase (spectralConeIndexFrequency p * x))
      (complexProductSlabQuotient s r ((x : ℂ) + (t : ℂ) * Complex.I) +
        -complexProductSlabQuotient s r ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) := by
    apply HasSum.sum
    · apply hu.congr_fun
      intro p
      rw [complexUnitPhase_damped_upper (positiveConeFrequency_nonneg p)]
      change (atomicExponentialDamping (positiveConeFrequency p) t : ℂ) *
        productConeIndexCoefficient s r (.inl p) * unitPhase (positiveConeFrequency p * x) = _
      ring
    · convert! hn using 1
  convert! hsum using 1
  unfold productTubeJump
  rw [show (x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
    (x : ℂ) - (t : ℂ) * Complex.I by push_cast; ring]
  rfl

/-- The complete actual coarse carrier series, without duplicating zero, equals the
actual quotient jump for every positive tube height. -/
theorem productDampedSpectral_hasSum_jump (s : ℕ) (r : productNumeratorIndex s → ℂ)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun y : spectralConeCarrier.subtype =>
      dampedAtomicCoefficient spectralConeCarrier (productSpectralCoefficient s r) t y *
        unitPhase ((y : ℝ) * x)) (productTubeJump s r t x) := by
  apply spectralConeEquiv.hasSum_iff.mp
  convert! productDampedConeIndex_hasSum s r ht x using 1
  funext p
  change (atomicExponentialDamping (spectralConeIndexFrequency p) t : ℂ) *
    productSpectralCoefficient s r (spectralConeIndexPoint p) *
      unitPhase (spectralConeIndexFrequency p * x) = _
  rw [productSpectralCoefficient_at_label]

end

end MeyerGeneralProblem.StrongParity
