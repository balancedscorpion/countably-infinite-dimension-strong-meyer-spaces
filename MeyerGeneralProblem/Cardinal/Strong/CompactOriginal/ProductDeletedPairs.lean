module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.PhysicalDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductOriginalRows
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPairClassification
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPairFiniteDimension
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductDeletedPairs

@[expose] public section

/-! Complete original ProductDeletedPairs for actual compact parameter blocks.
Every original supported pair is retained, without a constructed-image premise. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open scoped FourierTransform

theorem productOriginalDeletedPairSpace_le_pair {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    productOriginalDeletedPairSpace block E F ≤ productOriginalPairSpace block := by
  intro T hT
  change AtomicOnCarrier ((compactOriginalProductSheetCarrier block).delete E) T ∧
    AtomicOnCarrier (spectralConeCarrier.delete F) (𝓕 T) at hT
  exact ⟨hT.1.mono Set.sdiff_subset, hT.2.mono Set.sdiff_subset⟩

/-- Synthesis from the FULL original deletion kernel to the ACTUAL whole
deleted-support pair space. -/
def productOriginalDeletedPairConstructionMap {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    productOriginalDeletionKernel block E F →ₗ[ℂ] productOriginalDeletedPairSpace block E F :=
  ((productPhysicalDistributionLinearMap block).comp
    (productOriginalDeletionKernel block E F).subtype).codRestrict
      (productOriginalDeletedPairSpace block E F)
      (fun r => (productPhysical_mem_deletedPairSpace_iff block E F r).mpr r.property)

theorem productOriginalDeletedPairConstructionMap_coe {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ)
    (r : productOriginalDeletionKernel block E F) :
    (productOriginalDeletedPairConstructionMap block E F r : TemperedDistribution ℝ ℂ) =
      productPhysicalDistribution block r := rfl

theorem productOriginalDeletedPairConstructionMap_bijective {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    Function.Bijective (productOriginalDeletedPairConstructionMap block E F) := by
  constructor
  · intro r t h
    apply Subtype.ext
    apply productPhysicalDistribution_injective block
    exact congrArg Subtype.val h
  · intro T
    let U : productOriginalPairSpace block :=
      ⟨T.val, productOriginalDeletedPairSpace_le_pair block E F T.property⟩
    let r := productOriginalPairNumeratorMap block U
    have hr : r ∈ productOriginalDeletionKernel block E F := by
      apply (productPhysical_mem_deletedPairSpace_iff block E F r).mp
      rw [← productOriginalPair_recovery block U]
      exact T.property
    refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
    exact (productOriginalPair_recovery block U).symm

/-- The COMPLETE deleted pair space is the FULL original row kernel,
without a forward-image, admission or completeness premise. -/
def productOriginalDeletedPairEquiv {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    productOriginalDeletedPairSpace block E F ≃ₗ[ℂ] productOriginalDeletionKernel block E F :=
  (LinearEquiv.ofBijective (productOriginalDeletedPairConstructionMap block E F)
    (productOriginalDeletedPairConstructionMap_bijective block E F)).symm

theorem productOriginalDeletedPairSpace_finrank_eq_kernel {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    Module.finrank ℂ (productOriginalDeletedPairSpace block E F) =
      Module.finrank ℂ (productOriginalDeletionKernel block E F) :=
  (productOriginalDeletedPairEquiv block E F).finrank_eq

theorem productOriginalDeletedPair_physical_mem_strongExponent {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ)
    (T : productOriginalDeletedPairSpace block E F) :
    (T : TemperedDistribution ℝ ℂ) ∈
      stronglyTemperedAtomicAtExponent ((compactOriginalProductSheetCarrier block).delete E) ((s - 1) + 2) :=
  stronglyTemperedAtomicAtExponent_delete _ _ _ _ T.property.1
    (productOriginalPair_physical_mem_strongExponent block
      ⟨T.val, productOriginalDeletedPairSpace_le_pair block E F T.property⟩)

theorem productOriginalDeletedPair_spectral_mem_strongExponent {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ)
    (T : productOriginalDeletedPairSpace block E F) :
    𝓕 (T : TemperedDistribution ℝ ℂ) ∈
      stronglyTemperedAtomicAtExponent (spectralConeCarrier.delete F) (s + 3) :=
  stronglyTemperedAtomicAtExponent_delete _ _ _ _ T.property.2
    (productOriginalPair_spectral_mem_strongExponent block
      ⟨T.val, productOriginalDeletedPairSpace_le_pair block E F T.property⟩)

theorem productOriginalDeletedPair_both_strong {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ)
    (T : productOriginalDeletedPairSpace block E F) :
    (T : TemperedDistribution ℝ ℂ) ∈ StronglyTemperedAtomicOnCarrier
      ((compactOriginalProductSheetCarrier block).delete E) ∧
    𝓕 (T : TemperedDistribution ℝ ℂ) ∈ StronglyTemperedAtomicOnCarrier
      (spectralConeCarrier.delete F) := by
  constructor
  · exact (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
      ⟨_, productOriginalDeletedPair_physical_mem_strongExponent block E F T⟩
  · exact (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
      ⟨_, productOriginalDeletedPair_spectral_mem_strongExponent block E F T⟩

/-- Both ORIGINAL records strongly tempered on the actual two deleted carriers. -/
def productOriginalStrongDeletedPairSpace {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  StronglyTemperedAtomicOnCarrier ((compactOriginalProductSheetCarrier block).delete E) ⊓
    (StronglyTemperedAtomicOnCarrier (spectralConeCarrier.delete F)).comap
      temperedFourierLinearMap

theorem productOriginalStrongDeletedPairSpace_eq_pair {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    productOriginalStrongDeletedPairSpace block E F = productOriginalDeletedPairSpace block E F := by
  apply le_antisymm
  · intro T hT
    obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT.1
    obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hT.2
    exact ⟨hasLocallyAtomicAction_atomicOnCarrier _ _ hN.1,
      hasLocallyAtomicAction_atomicOnCarrier _ _ hM.1⟩
  · intro T hT
    exact productOriginalDeletedPair_both_strong block E F ⟨T, hT⟩

/-- The whole original strong deleted pair space, rather than its constructed
image, is linearly equivalent to the complete original row kernel. -/
def productOriginalStrongDeletedPairEquiv {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    productOriginalStrongDeletedPairSpace block E F ≃ₗ[ℂ] productOriginalDeletionKernel block E F :=
  (LinearEquiv.ofEq _ _ (productOriginalStrongDeletedPairSpace_eq_pair block E F)).trans
    (productOriginalDeletedPairEquiv block E F)

theorem productOriginalStrongDeletedPairSpace_finrank_eq_kernel {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    Module.finrank ℂ (productOriginalStrongDeletedPairSpace block E F) =
      Module.finrank ℂ (productOriginalDeletionKernel block E F) :=
  (productOriginalStrongDeletedPairEquiv block E F).finrank_eq

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
