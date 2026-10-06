module

public import MeyerGeneralProblem.Cardinal.Strong.ProductOriginalRows

@[expose] public section

/-! Complete classification after ORIGINAL physical and spectral deletions.
Every arbitrary pair is recovered in the complete slab row kernel; both original
weighted variation estimates descend to the actual restricted carriers. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped FourierTransform

theorem productOriginalDeletedPairSpace_le_pair (s : ℕ) (E F : Set ℝ) :
    productOriginalDeletedPairSpace s E F ≤ productOriginalPairSpace s := by
  intro T hT
  change AtomicOnCarrier ((productSheetCarrier s).delete E) T ∧
    AtomicOnCarrier (spectralConeCarrier.delete F) (𝓕 T) at hT
  exact ⟨hT.1.mono Set.sdiff_subset, hT.2.mono Set.sdiff_subset⟩

/-- Synthesis from the FULL original deletion kernel to the ACTUAL whole
deleted-support pair space. -/
def productOriginalDeletedPairConstructionMap (s : ℕ) (E F : Set ℝ) :
    productOriginalDeletionKernel s E F →ₗ[ℂ] productOriginalDeletedPairSpace s E F :=
  ((productPhysicalDistributionLinearMap s).comp
    (productOriginalDeletionKernel s E F).subtype).codRestrict
      (productOriginalDeletedPairSpace s E F)
      (fun r => (productPhysical_mem_deletedPairSpace_iff s E F r).mpr r.property)

theorem productOriginalDeletedPairConstructionMap_coe (s : ℕ) (E F : Set ℝ)
    (r : productOriginalDeletionKernel s E F) :
    (productOriginalDeletedPairConstructionMap s E F r : TemperedDistribution ℝ ℂ) =
      productPhysicalDistribution s r := rfl

theorem productOriginalDeletedPairConstructionMap_bijective (s : ℕ) (E F : Set ℝ) :
    Function.Bijective (productOriginalDeletedPairConstructionMap s E F) := by
  constructor
  · intro r t h
    apply Subtype.ext
    apply productPhysicalDistribution_injective s
    exact congrArg Subtype.val h
  · intro T
    let U : productOriginalPairSpace s :=
      ⟨T.val, productOriginalDeletedPairSpace_le_pair s E F T.property⟩
    let r := productOriginalPairNumeratorMap s U
    have hr : r ∈ productOriginalDeletionKernel s E F := by
      apply (productPhysical_mem_deletedPairSpace_iff s E F r).mp
      rw [← productOriginalPair_recovery s U]
      exact T.property
    refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
    exact (productOriginalPair_recovery s U).symm

/-- The COMPLETE deleted pair space is the FULL original row kernel,
without a forward-image, admission or completeness premise. -/
def productOriginalDeletedPairEquiv (s : ℕ) (E F : Set ℝ) :
    productOriginalDeletedPairSpace s E F ≃ₗ[ℂ] productOriginalDeletionKernel s E F :=
  (LinearEquiv.ofBijective (productOriginalDeletedPairConstructionMap s E F)
    (productOriginalDeletedPairConstructionMap_bijective s E F)).symm

instance productOriginalDeletedPairSpace_finiteDimensional (s : ℕ) (E F : Set ℝ) :
    FiniteDimensional ℂ (productOriginalDeletedPairSpace s E F) :=
  Module.Finite.equiv (productOriginalDeletedPairEquiv s E F).symm

theorem productOriginalDeletedPairSpace_finrank_eq_kernel (s : ℕ) (E F : Set ℝ) :
    Module.finrank ℂ (productOriginalDeletedPairSpace s E F) =
      Module.finrank ℂ (productOriginalDeletionKernel s E F) :=
  (productOriginalDeletedPairEquiv s E F).finrank_eq

theorem productOriginalDeletedPair_physical_mem_strongExponent (s : ℕ) (E F : Set ℝ)
    (T : productOriginalDeletedPairSpace s E F) :
    (T : TemperedDistribution ℝ ℂ) ∈
      stronglyTemperedAtomicAtExponent ((productSheetCarrier s).delete E) ((s - 1) + 2) :=
  stronglyTemperedAtomicAtExponent_delete _ _ _ _ T.property.1
    (productOriginalPair_physical_mem_strongExponent s
      ⟨T.val, productOriginalDeletedPairSpace_le_pair s E F T.property⟩)

theorem productOriginalDeletedPair_spectral_mem_strongExponent (s : ℕ) (E F : Set ℝ)
    (T : productOriginalDeletedPairSpace s E F) :
    𝓕 (T : TemperedDistribution ℝ ℂ) ∈
      stronglyTemperedAtomicAtExponent (spectralConeCarrier.delete F) (s + 3) :=
  stronglyTemperedAtomicAtExponent_delete _ _ _ _ T.property.2
    (productOriginalPair_spectral_mem_strongExponent s
      ⟨T.val, productOriginalDeletedPairSpace_le_pair s E F T.property⟩)

theorem productOriginalDeletedPair_both_strong (s : ℕ) (E F : Set ℝ)
    (T : productOriginalDeletedPairSpace s E F) :
    (T : TemperedDistribution ℝ ℂ) ∈ StronglyTemperedAtomicOnCarrier
      ((productSheetCarrier s).delete E) ∧
    𝓕 (T : TemperedDistribution ℝ ℂ) ∈ StronglyTemperedAtomicOnCarrier
      (spectralConeCarrier.delete F) := by
  constructor
  · exact (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
      ⟨_, productOriginalDeletedPair_physical_mem_strongExponent s E F T⟩
  · exact (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
      ⟨_, productOriginalDeletedPair_spectral_mem_strongExponent s E F T⟩

/-- Both ORIGINAL records strongly tempered on the actual two deleted carriers. -/
def productOriginalStrongDeletedPairSpace (s : ℕ) (E F : Set ℝ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  StronglyTemperedAtomicOnCarrier ((productSheetCarrier s).delete E) ⊓
    (StronglyTemperedAtomicOnCarrier (spectralConeCarrier.delete F)).comap
      temperedFourierLinearMap

theorem productOriginalStrongDeletedPairSpace_eq_pair (s : ℕ) (E F : Set ℝ) :
    productOriginalStrongDeletedPairSpace s E F = productOriginalDeletedPairSpace s E F := by
  apply le_antisymm
  · intro T hT
    obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT.1
    obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hT.2
    exact ⟨hasLocallyAtomicAction_atomicOnCarrier _ _ hN.1,
      hasLocallyAtomicAction_atomicOnCarrier _ _ hM.1⟩
  · intro T hT
    exact productOriginalDeletedPair_both_strong s E F ⟨T, hT⟩

/-- The whole original strong deleted pair space, rather than its constructed
image, is linearly equivalent to the complete original row kernel. -/
def productOriginalStrongDeletedPairEquiv (s : ℕ) (E F : Set ℝ) :
    productOriginalStrongDeletedPairSpace s E F ≃ₗ[ℂ] productOriginalDeletionKernel s E F :=
  (LinearEquiv.ofEq _ _ (productOriginalStrongDeletedPairSpace_eq_pair s E F)).trans
    (productOriginalDeletedPairEquiv s E F)

theorem productOriginalStrongDeletedPairSpace_finrank_eq_kernel (s : ℕ) (E F : Set ℝ) :
    Module.finrank ℂ (productOriginalStrongDeletedPairSpace s E F) =
      Module.finrank ℂ (productOriginalDeletionKernel s E F) :=
  (productOriginalStrongDeletedPairEquiv s E F).finrank_eq

end

end MeyerGeneralProblem.StrongParity
