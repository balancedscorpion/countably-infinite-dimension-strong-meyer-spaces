module

public import MeyerGeneralProblem.Cardinal.Strong.ProductAnnihilator
public import MeyerGeneralProblem.Cardinal.Strong.SpectralCone

@[expose] public section

/-! Finite original numerators and injectivity for EVERY original supported
Fourier pair on the actual complete product-root / coarse-cone carriers. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped SchwartzMap FourierTransform

/-- Both signs of the complete original cone lie in the actual integer lattice. -/
theorem spectralCone_subset_rankTwoFrequencyRange :
    spectralConeCarrier.carrier ⊆ Set.range rankTwoFrequencyHom := by
  rintro x ⟨⟨b, k, n⟩, rfl⟩
  cases b
  · refine ⟨((k : ℤ), (n : ℤ)), ?_⟩
    simp [rankTwoFrequencyHom, signedConeFrequency, positiveConeFrequency]
  · refine ⟨(-(k : ℤ), -(n : ℤ)), ?_⟩
    simp [rankTwoFrequencyHom, signedConeFrequency, positiveConeFrequency, mul_neg, add_comm]

/-- The literal Laurent recurrence holds for an ARBITRARY actual original
product-root / coarse-cone Fourier pair. -/
theorem product_originalFourierArray_annihilated (s : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (productSheetCarrier s) T)
    (hFT : AtomicOnCarrier spectralConeCarrier (𝓕 T)) :
    ∀ n, annihilatorArrayConvolution (productLaurentCoefficients s)
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T) n = 0 :=
  originalFourierArray_annihilated rankTwoFrequencyHom (productLaurentCoefficients s)
    (productSheetCarrier s) spectralConeCarrier T hT hFT (productLaurentSymbol_vanishes s)

/-- The finite numerator theorem applies to the ENTIRE actual supported pair
space, for every cut; no slab certificate or constructed-image premise remains. -/
theorem product_originalFourierPair_exists_finite_numerator (s : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (productSheetCarrier s) T)
    (hFT : AtomicOnCarrier spectralConeCarrier (𝓕 T)) (cut : ℝ) :
    ∃ R : (ℤ × ℤ) →₀ ℂ, ∀ n,
      R n = annihilatorArrayConvolution (productLaurentCoefficients s)
        (arrayPositiveCut rankTwoFrequencyHom cut
          (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T)) n ∧
      R n = -annihilatorArrayConvolution (productLaurentCoefficients s)
        (arrayNegativeCut rankTwoFrequencyHom cut
          (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T)) n :=
  originalFourierPair_exists_finite_numerator rankTwoFrequencyHom rankTwoFrequencyHom_injective
    (productLaurentCoefficients s) (productLaurentCoefficients_ne_zero s)
    (productSheetCarrier s) spectralConeCarrier T hT hFT (productLaurentSymbol_vanishes s) cut

/-- Equality of actual cut numerators forces equality of arbitrary original
supported Fourier pairs on the complete carriers. -/
theorem product_originalFourierPair_cutNumerator_injective (s : ℕ)
    (T U : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (productSheetCarrier s) T)
    (hU : AtomicOnCarrier (productSheetCarrier s) U)
    (hFT : AtomicOnCarrier spectralConeCarrier (𝓕 T))
    (hFU : AtomicOnCarrier spectralConeCarrier (𝓕 U)) (cut : ℝ)
    (heq : cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients s) cut
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T) =
      cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients s) cut
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier U)) : T = U :=
  originalFourierPair_cutNumerator_injective rankTwoFrequencyHom rankTwoFrequencyHom_injective
    (productLaurentCoefficients s) (productLaurentCoefficients_ne_zero s)
    (productSheetCarrier s) spectralConeCarrier spectralCone_subset_rankTwoFrequencyRange
    T U hT hU hFT hFU (productLaurentSymbol_vanishes s) cut heq

end

end MeyerGeneralProblem.StrongParity
