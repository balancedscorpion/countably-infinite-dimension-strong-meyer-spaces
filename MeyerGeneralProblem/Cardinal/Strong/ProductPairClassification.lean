module

public import MeyerGeneralProblem.Cardinal.Strong.ProductInverseNumerator

@[expose] public section

/-! Complete one-product classification of arbitrary original supported Fourier
pairs. The actual physical construction and original numerator map are inverse;
both ORIGINAL records satisfy explicit absolute weighted TV bounds. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped FourierTransform

theorem productPhysical_mem_originalPairSpace (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    productPhysicalDistribution s r ∈ productOriginalPairSpace s := by
  change AtomicOnCarrier (productSheetCarrier s) (productPhysicalDistribution s r) ∧
    AtomicOnCarrier spectralConeCarrier (𝓕 (productPhysicalDistribution s r))
  exact ⟨productPhysicalDistribution_atomicOnCarrier s r,
    by rw [productPhysical_fourier_eq_spectral]; exact productSpectralDistribution_atomicOnCarrier s r⟩

/-- Every original slab maps to its actual original supported Fourier pair. -/
def productOriginalPairConstructionMap (s : ℕ) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] productOriginalPairSpace s :=
  (productPhysicalDistributionLinearMap s).codRestrict (productOriginalPairSpace s)
    (productPhysical_mem_originalPairSpace s)

theorem productOriginalPairConstructionMap_coe (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    (productOriginalPairConstructionMap s r : TemperedDistribution ℝ ℂ) =
      productPhysicalDistribution s r := rfl

/-- The original finite numerator recovers EVERY coefficient of the slab. -/
theorem productOriginalPairNumeratorMap_construction (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    productOriginalPairNumeratorMap s (productOriginalPairConstructionMap s r) = r := by
  funext ij
  change cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients s) 0
    (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
      (productPhysicalDistribution s r)) (productNumeratorIntegerIndex s ij) /
    complexUnitPhase (-1 / 4) ^ (ij.val.2 : ℕ) = r ij
  rw [productPhysical_cutNumerator_eq_slab, productSlabLaurentPolynomial_coefficient]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ (Complex.exp_ne_zero _))

theorem productOriginalPairNumeratorMap_surjective (s : ℕ) :
    Function.Surjective (productOriginalPairNumeratorMap s) :=
  fun r => ⟨productOriginalPairConstructionMap s r, productOriginalPairNumeratorMap_construction s r⟩

/-- Recovery of an ARBITRARY original pair; there is no constructed-image
premise, and the equality is between entire tempered distributions. -/
theorem productOriginalPairConstructionMap_numerator (s : ℕ) (T : productOriginalPairSpace s) :
    productOriginalPairConstructionMap s (productOriginalPairNumeratorMap s T) = T := by
  apply productOriginalPairNumeratorMap_injective s
  exact productOriginalPairNumeratorMap_construction s _

/-- The COMPLETE original root/cone pair space is complex-linearly equivalent
to the full original Newton slab with just the top corner removed. -/
def productOriginalPairEquiv (s : ℕ) :
    productOriginalPairSpace s ≃ₗ[ℂ] (productNumeratorIndex s → ℂ) :=
  LinearEquiv.ofBijective (productOriginalPairNumeratorMap s)
    ⟨productOriginalPairNumeratorMap_injective s, productOriginalPairNumeratorMap_surjective s⟩

theorem productOriginalPairSpace_finrank_eq (s : ℕ) :
    Module.finrank ℂ (productOriginalPairSpace s) = (s + 1) ^ 2 - 1 := by
  simpa only [Module.finrank_fintype_fun_eq_card, productNumeratorIndex_card] using
    (productOriginalPairEquiv s).finrank_eq

theorem productPhysicalDistribution_injective (s : ℕ) :
    Function.Injective (productPhysicalDistribution s) := by
  intro r t h
  have hp : productOriginalPairConstructionMap s r = productOriginalPairConstructionMap s t :=
    Subtype.ext h
  simpa only [productOriginalPairNumeratorMap_construction] using
    congrArg (productOriginalPairNumeratorMap s) hp

theorem productOriginalPair_recovery (s : ℕ) (T : productOriginalPairSpace s) :
    (T : TemperedDistribution ℝ ℂ) =
      productPhysicalDistribution s (productOriginalPairNumeratorMap s T) :=
  (congrArg Subtype.val (productOriginalPairConstructionMap_numerator s T)).symm

/-- Every arbitrary original root/cone pair has a UNIQUE original slab
representation. The Fourier pair hypotheses are the actual vanishing ideals. -/
theorem productOriginalPair_exists_unique_slab (s : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (productSheetCarrier s) T)
    (hFT : AtomicOnCarrier spectralConeCarrier (𝓕 T)) :
    ∃! r : productNumeratorIndex s → ℂ, T = productPhysicalDistribution s r := by
  let t : productOriginalPairSpace s := ⟨T, ⟨hT, hFT⟩⟩
  refine ⟨productOriginalPairNumeratorMap s t, productOriginalPair_recovery s t, ?_⟩
  intro r hr
  apply productPhysicalDistribution_injective s
  exact hr.symm.trans (productOriginalPair_recovery s t)

/-- Actual strong admission of EVERY original physical record in the complete
space, at an explicit proved exponent rather than an existential certificate. -/
theorem productOriginalPair_physical_mem_strongExponent (s : ℕ) (T : productOriginalPairSpace s) :
    (T : TemperedDistribution ℝ ℂ) ∈
      stronglyTemperedAtomicAtExponent (productSheetCarrier s) ((s - 1) + 2) := by
  rw [productOriginalPair_recovery s T]
  exact productPhysicalDistribution_mem_strongExponent s _

/-- Actual strong admission of EVERY original Fourier record, with both
original signs and zero counted once in the complete spectral carrier. -/
theorem productOriginalPair_spectral_mem_strongExponent (s : ℕ) (T : productOriginalPairSpace s) :
    𝓕 (T : TemperedDistribution ℝ ℂ) ∈
      stronglyTemperedAtomicAtExponent spectralConeCarrier (s + 3) := by
  rw [productOriginalPair_recovery s T, productPhysical_fourier_eq_spectral]
  exact productSpectralDistribution_mem_strongExponent s _

theorem productOriginalPair_both_strong (s : ℕ) (T : productOriginalPairSpace s) :
    (T : TemperedDistribution ℝ ℂ) ∈ StronglyTemperedAtomicOnCarrier (productSheetCarrier s) ∧
      𝓕 (T : TemperedDistribution ℝ ℂ) ∈ StronglyTemperedAtomicOnCarrier spectralConeCarrier := by
  constructor
  · exact (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
      ⟨(s - 1) + 2, productOriginalPair_physical_mem_strongExponent s T⟩
  · exact (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
      ⟨s + 3, productOriginalPair_spectral_mem_strongExponent s T⟩

end

end MeyerGeneralProblem.StrongParity
