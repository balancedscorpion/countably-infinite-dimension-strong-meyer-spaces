module

public import MeyerGeneralProblem.Distribution.FiniteCombConvolutionSupport

@[expose] public section

/-!
# Finite exponential annihilators of actual atomic Fourier pairs

The finite symbol is a genuine Schwartz multiplier. Vanishing on the physical
carrier annihilates every original atomic distribution, and Fourier transform
gives an actual finite convolution of its original spectral distribution.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped SchwartzMap FourierTransform

/-- Fourier sends positive character multiplication to positive translation. -/
theorem fourier_combDistributionModulation (a : ℝ) (T : TemperedDistribution ℝ ℂ) :
    𝓕 (combDistributionModulation a T) = combDistributionTranslation a (𝓕 T) := by
  ext f
  simp only [TemperedDistribution.fourier_apply, combDistributionModulation_apply,
    combDistributionTranslation_apply]
  congr 1
  ext x
  rw [combSchwartzModulation_apply, fourier_combSchwartzTranslation]

/-- Multiplication by the literal positive-phase finite exponential symbol. -/
def finiteExponentialMultiplication {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  ∑ i, c i • combDistributionModulation (a i)

theorem finiteExponentialMultiplication_apply {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    finiteExponentialMultiplication a c T f =
      T (finiteCombSchwartzSymbol (fun i => -a i) c f) := by
  simp only [finiteExponentialMultiplication, _root_.sum_apply, smul_apply,
    combDistributionModulation_apply, finiteCombSchwartzSymbol, neg_neg,
    map_sum, map_smul]

/-- The actual Fourier convolution identity has no support or growth premise. -/
theorem fourier_finiteExponentialMultiplication {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (T : TemperedDistribution ℝ ℂ) :
    𝓕 (finiteExponentialMultiplication a c T) = finiteCombConvolution a c (𝓕 T) := by
  change temperedFourierLinearMap _ = _
  simp only [finiteExponentialMultiplication, map_sum, map_smul,
    temperedFourierLinearMap_apply, fourier_combDistributionModulation,
    finiteCombConvolution, _root_.sum_apply, _root_.smul_apply]

/-- A finite exponential symbol vanishing on the original physical carrier
annihilates every actual value-only atomic distribution there. -/
theorem finiteExponentialMultiplication_eq_zero {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T) (a : ι → ℝ) (c : ι → ℂ)
    (hz : ∀ x ∈ S.carrier, ∑ i, c i * combModulationCharacter (a i) x = 0) :
    finiteExponentialMultiplication a c T = 0 := by
  ext f
  rw [finiteExponentialMultiplication_apply]
  apply hT
  intro x hx
  rw [finiteCombSchwartzSymbol_apply]
  simp only [finiteCombFourierSymbol, neg_neg]
  rw [hz x hx, zero_mul]

/-- The original Fourier distribution satisfies its actual finite-shift
equation; neither a constructed forward image nor a certificate is assumed. -/
theorem finiteCombConvolution_fourier_eq_zero {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T) (a : ι → ℝ) (c : ι → ℂ)
    (hz : ∀ x ∈ S.carrier, ∑ i, c i * combModulationCharacter (a i) x = 0) :
    finiteCombConvolution a c (𝓕 T) = 0 := by
  rw [← fourier_finiteExponentialMultiplication,
    finiteExponentialMultiplication_eq_zero S T hT a c hz]
  exact FourierTransform.fourier_zero

end

end MeyerGeneralProblem
