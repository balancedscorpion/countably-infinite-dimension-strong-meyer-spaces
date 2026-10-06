module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductAnnihilator
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductReverseNumerator

@[expose] public section

/-! Complete original ProductReverseNumerator for actual compact parameter blocks.
Every original supported pair is retained, without a constructed-image premise. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open scoped SchwartzMap FourierTransform

/-- The literal Laurent recurrence holds for an ARBITRARY actual original
product-root / coarse-cone Fourier pair. -/
theorem product_originalFourierArray_annihilated {s : ℕ} (block : CompactOriginalParameterBlock s) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (compactOriginalProductSheetCarrier block) T)
    (hFT : AtomicOnCarrier spectralConeCarrier (𝓕 T)) :
    ∀ n, annihilatorArrayConvolution (productLaurentCoefficients block)
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T) n = 0 :=
  originalFourierArray_annihilated rankTwoFrequencyHom (productLaurentCoefficients block)
    (compactOriginalProductSheetCarrier block) spectralConeCarrier T hT hFT (productLaurentSymbol_vanishes block)

/-- The finite numerator theorem applies to the ENTIRE actual supported pair
space, for every cut; no slab certificate or constructed-image premise remains. -/
theorem product_originalFourierPair_exists_finite_numerator {s : ℕ} (block : CompactOriginalParameterBlock s)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (compactOriginalProductSheetCarrier block) T)
    (hFT : AtomicOnCarrier spectralConeCarrier (𝓕 T)) (cut : ℝ) :
    ∃ R : (ℤ × ℤ) →₀ ℂ, ∀ n,
      R n = annihilatorArrayConvolution (productLaurentCoefficients block)
        (arrayPositiveCut rankTwoFrequencyHom cut
          (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T)) n ∧
      R n = -annihilatorArrayConvolution (productLaurentCoefficients block)
        (arrayNegativeCut rankTwoFrequencyHom cut
          (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T)) n :=
  originalFourierPair_exists_finite_numerator rankTwoFrequencyHom rankTwoFrequencyHom_injective
    (productLaurentCoefficients block) (productLaurentCoefficients_ne_zero block)
    (compactOriginalProductSheetCarrier block) spectralConeCarrier T hT hFT (productLaurentSymbol_vanishes block) cut

/-- Equality of actual cut numerators forces equality of arbitrary original
supported Fourier pairs on the complete carriers. -/
theorem product_originalFourierPair_cutNumerator_injective {s : ℕ} (block : CompactOriginalParameterBlock s)
    (T U : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (compactOriginalProductSheetCarrier block) T)
    (hU : AtomicOnCarrier (compactOriginalProductSheetCarrier block) U)
    (hFT : AtomicOnCarrier spectralConeCarrier (𝓕 T))
    (hFU : AtomicOnCarrier spectralConeCarrier (𝓕 U)) (cut : ℝ)
    (heq : cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients block) cut
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T) =
      cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients block) cut
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier U)) : T = U :=
  originalFourierPair_cutNumerator_injective rankTwoFrequencyHom rankTwoFrequencyHom_injective
    (productLaurentCoefficients block) (productLaurentCoefficients_ne_zero block)
    (compactOriginalProductSheetCarrier block) spectralConeCarrier spectralCone_subset_rankTwoFrequencyRange
    T U hT hU hFT hFU (productLaurentSymbol_vanishes block) cut heq

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
