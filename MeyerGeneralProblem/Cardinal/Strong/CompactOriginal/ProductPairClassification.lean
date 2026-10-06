module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.PhysicalDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductAnnihilator
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductFourierPair
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductInverseNumerator
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPairFiniteDimension
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductPairClassification

@[expose] public section

/-! Complete original ProductPairClassification for actual compact parameter blocks.
Every original supported pair is retained, without a constructed-image premise. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open scoped FourierTransform

theorem productPhysical_mem_originalPairSpace {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    productPhysicalDistribution block r ∈ productOriginalPairSpace block := by
  change AtomicOnCarrier (compactOriginalProductSheetCarrier block) (productPhysicalDistribution block r) ∧
    AtomicOnCarrier spectralConeCarrier (𝓕 (productPhysicalDistribution block r))
  exact ⟨productPhysicalDistribution_atomicOnCarrier block r,
    by rw [productPhysical_fourier_eq_spectral]; exact productSpectralDistribution_atomicOnCarrier block r⟩

/-- Every original slab maps to its actual original supported Fourier pair. -/
def productOriginalPairConstructionMap {s : ℕ} (block : CompactOriginalParameterBlock s) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] productOriginalPairSpace block :=
  (productPhysicalDistributionLinearMap block).codRestrict (productOriginalPairSpace block)
    (productPhysical_mem_originalPairSpace block)

theorem productOriginalPairConstructionMap_coe {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    (productOriginalPairConstructionMap block r : TemperedDistribution ℝ ℂ) =
      productPhysicalDistribution block r := rfl

/-- The original finite numerator recovers EVERY coefficient of the slab. -/
theorem productOriginalPairNumeratorMap_construction {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    productOriginalPairNumeratorMap block (productOriginalPairConstructionMap block r) = r := by
  funext ij
  change cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients block) 0
    (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
      (productPhysicalDistribution block r)) (productNumeratorIntegerIndex s ij) /
    complexUnitPhase (-1 / 4) ^ (ij.val.2 : ℕ) = r ij
  rw [productPhysical_cutNumerator_eq_slab, productSlabLaurentPolynomial_coefficient]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ (Complex.exp_ne_zero _))

theorem productOriginalPairNumeratorMap_surjective {s : ℕ} (block : CompactOriginalParameterBlock s) :
    Function.Surjective (productOriginalPairNumeratorMap block) :=
  fun r => ⟨productOriginalPairConstructionMap block r, productOriginalPairNumeratorMap_construction block r⟩

/-- Recovery of an ARBITRARY original pair; there is no constructed-image
premise, and the equality is between entire tempered distributions. -/
theorem productOriginalPairConstructionMap_numerator {s : ℕ} (block : CompactOriginalParameterBlock s) (T : productOriginalPairSpace block) :
    productOriginalPairConstructionMap block (productOriginalPairNumeratorMap block T) = T := by
  apply productOriginalPairNumeratorMap_injective block
  exact productOriginalPairNumeratorMap_construction block _

/-- The COMPLETE original root/cone pair space is complex-linearly equivalent
to the full original Newton slab with just the top corner removed. -/
def productOriginalPairEquiv {s : ℕ} (block : CompactOriginalParameterBlock s) :
    productOriginalPairSpace block ≃ₗ[ℂ] (productNumeratorIndex s → ℂ) :=
  LinearEquiv.ofBijective (productOriginalPairNumeratorMap block)
    ⟨productOriginalPairNumeratorMap_injective block, productOriginalPairNumeratorMap_surjective block⟩

theorem productOriginalPairSpace_finrank_eq {s : ℕ} (block : CompactOriginalParameterBlock s) :
    Module.finrank ℂ (productOriginalPairSpace block) = (s + 1) ^ 2 - 1 := by
  simpa only [Module.finrank_fintype_fun_eq_card, productNumeratorIndex_card] using
    (productOriginalPairEquiv block).finrank_eq

theorem productPhysicalDistribution_injective {s : ℕ} (block : CompactOriginalParameterBlock s) :
    Function.Injective (productPhysicalDistribution block) := by
  intro r t h
  have hp : productOriginalPairConstructionMap block r = productOriginalPairConstructionMap block t :=
    Subtype.ext h
  simpa only [productOriginalPairNumeratorMap_construction] using
    congrArg (productOriginalPairNumeratorMap block) hp

theorem productOriginalPair_recovery {s : ℕ} (block : CompactOriginalParameterBlock s) (T : productOriginalPairSpace block) :
    (T : TemperedDistribution ℝ ℂ) =
      productPhysicalDistribution block (productOriginalPairNumeratorMap block T) :=
  (congrArg Subtype.val (productOriginalPairConstructionMap_numerator block T)).symm

/-- Every arbitrary original root/cone pair has a UNIQUE original slab
representation. The Fourier pair hypotheses are the actual vanishing ideals. -/
theorem productOriginalPair_exists_unique_slab {s : ℕ} (block : CompactOriginalParameterBlock s) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (compactOriginalProductSheetCarrier block) T)
    (hFT : AtomicOnCarrier spectralConeCarrier (𝓕 T)) :
    ∃! r : productNumeratorIndex s → ℂ, T = productPhysicalDistribution block r := by
  let t : productOriginalPairSpace block := ⟨T, ⟨hT, hFT⟩⟩
  refine ⟨productOriginalPairNumeratorMap block t, productOriginalPair_recovery block t, ?_⟩
  intro r hr
  apply productPhysicalDistribution_injective block
  exact hr.symm.trans (productOriginalPair_recovery block t)

/-- Actual strong admission of EVERY original physical record in the complete
space, at an explicit proved exponent rather than an existential certificate. -/
theorem productOriginalPair_physical_mem_strongExponent {s : ℕ} (block : CompactOriginalParameterBlock s) (T : productOriginalPairSpace block) :
    (T : TemperedDistribution ℝ ℂ) ∈
      stronglyTemperedAtomicAtExponent (compactOriginalProductSheetCarrier block) ((s - 1) + 2) := by
  rw [productOriginalPair_recovery block T]
  exact productPhysicalDistribution_mem_strongExponent block _

/-- Actual strong admission of EVERY original Fourier record, with both
original signs and zero counted once in the complete spectral carrier. -/
theorem productOriginalPair_spectral_mem_strongExponent {s : ℕ} (block : CompactOriginalParameterBlock s) (T : productOriginalPairSpace block) :
    𝓕 (T : TemperedDistribution ℝ ℂ) ∈
      stronglyTemperedAtomicAtExponent spectralConeCarrier (s + 3) := by
  rw [productOriginalPair_recovery block T, productPhysical_fourier_eq_spectral]
  exact productSpectralDistribution_mem_strongExponent block _

theorem productOriginalPair_both_strong {s : ℕ} (block : CompactOriginalParameterBlock s) (T : productOriginalPairSpace block) :
    (T : TemperedDistribution ℝ ℂ) ∈ StronglyTemperedAtomicOnCarrier (compactOriginalProductSheetCarrier block) ∧
      𝓕 (T : TemperedDistribution ℝ ℂ) ∈ StronglyTemperedAtomicOnCarrier spectralConeCarrier := by
  constructor
  · exact (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
      ⟨(s - 1) + 2, productOriginalPair_physical_mem_strongExponent block T⟩
  · exact (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
      ⟨s + 3, productOriginalPair_spectral_mem_strongExponent block T⟩

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
