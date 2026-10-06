module

public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalWRootSearch
public import MeyerGeneralProblem.UniformDiscrete.OriginalDeterminantLine

@[expose] public section

/-! The PARTICULAR full-size original-root tuple returned by the implemented
search cuts the COMPLETE original strong pair space to one normalized line.
No second existential root selector or completeness premise is introduced. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- All physical rows of a prescribed full-size original-root tuple, on the whole H space. -/
def computedOriginalHeadRootRow {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) (roots : computedOriginalWIndex s hs m → Fin s × ℤ)
    (i : computedOriginalWIndex s hs m) :
    CompactOriginal.productOriginalHeadKernel block (computedOriginalHeadMask s m) →ₗ[ℂ] ℂ :=
  (CompactOriginal.productOriginalPhysicalRow block (compactOriginalRootPoint block (roots i))).comp
    (CompactOriginal.productOriginalHeadKernel block (computedOriginalHeadMask s m)).subtype

/-- The original literal corner functional on the COMPLETE computed-head kernel. -/
abbrev computedOriginalHeadCornerFunctional {s : ℕ} (block : CompactOriginalParameterBlock s)
    (m : ℕ) : CompactOriginal.productOriginalHeadKernel block (computedOriginalHeadMask s m) →ₗ[ℂ] ℂ :=
  (productCornerFunctional s).comp
    (CompactOriginal.productOriginalHeadKernel block (computedOriginalHeadMask s m)).subtype

/-- Specified WHOLE W basis, reindexed by the complete constructive computed index list. -/
def computedOriginalHeadCornerBasis {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) : Module.Basis (computedOriginalWIndex s hs m) ℂ
      (CompactOriginal.productOriginalHeadCornerKernel block (computedOriginalHeadMask s m)) :=
  (CompactOriginal.productOriginalHeadCornerFreeBasis block hs (computedOriginalHeadMask s m)).reindex
    (computedOriginalWIndexEquivActual block hs m).symm

/-- Reindexing retains each literal vector of the specified COMPLETE original W basis. -/
theorem computedOriginalHeadCornerBasis_apply {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) (j : computedOriginalWIndex s hs m) :
    computedOriginalHeadCornerBasis block hs m j =
      CompactOriginal.productOriginalHeadCornerFreeBasis block hs (computedOriginalHeadMask s m)
        (computedOriginalWIndexToActual block hs m j) := by
  unfold computedOriginalHeadCornerBasis
  rw [Module.Basis.reindex_apply]
  rfl

/-- The full corner-zero evaluation matrix is literally the ACTUAL computed original W matrix. -/
theorem computedOriginalHeadCornerEvaluationMatrix_eq {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) (roots : computedOriginalWIndex s hs m → Fin s × ℤ) :
    UniformDiscrete.originalCornerEvaluationMatrix (computedOriginalHeadRootRow block hs m roots)
      (computedOriginalHeadCornerFunctional block m) (computedOriginalHeadCornerBasis block hs m) =
        computedOriginalWRootMatrix block hs m roots := by
  unfold computedOriginalHeadCornerBasis computedOriginalWRootMatrix
  generalize hb : (CompactOriginal.productOriginalHeadCornerFreeBasis block hs
    (computedOriginalHeadMask s m)) = b
  ext i j
  change (computedOriginalHeadRootRow block hs m roots i)
    ((b.reindex (computedOriginalWIndexEquivActual block hs m).symm j).val) =
    CompactOriginal.productOriginalHeadCornerPhysicalRow block (computedOriginalHeadMask s m)
      (compactOriginalRootPoint block (roots i)) (b (computedOriginalWIndexToActual block hs m j))
  rw [Module.Basis.reindex_apply]
  rfl

/-- Actual finite root points of THIS prescribed original-root tuple. -/
def computedOriginalSelectedRootPoints {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) (roots : computedOriginalWIndex s hs m → Fin s × ℤ) :
    Finset (compactOriginalProductSheetCarrier block).subtype :=
  Finset.univ.image (fun i => compactOriginalRootPoint block (roots i))

/-- Actual physical deletion set of THIS prescribed finite original-root tuple. -/
def computedOriginalSelectedPhysicalDeletion {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) (roots : computedOriginalWIndex s hs m → Fin s × ℤ) : Set ℝ :=
  CompactOriginal.productSelectedPhysicalDeletion block (computedOriginalSelectedRootPoints block hs m roots)

/-- The selected actual root set has the exact complete W cardinality when labels are distinct. -/
theorem computedOriginalSelectedRootPoints_card {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) (roots : computedOriginalWIndex s hs m → Fin s × ℤ)
    (hi : Function.Injective roots) :
    (computedOriginalSelectedRootPoints block hs m roots).card +
      (computedOriginalNoncoarseHeadLabels s m).card + 2 = (s + 1) ^ 2 := by
  have hi' : Function.Injective (fun i => compactOriginalRootPoint block (roots i)) :=
    (compactOriginalRootPoint_bijective block).1.comp hi
  rw [computedOriginalSelectedRootPoints, Finset.card_image_of_injective _ hi', Finset.card_univ]
  exact computedOriginalWIndex_card block hs m

/-- EVERY full deletion row is equivalent to the selected root equations on the WHOLE H kernel. -/
theorem computedOriginalHeadRootKernel_eq_comap {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) (roots : computedOriginalWIndex s hs m → Fin s × ℤ) :
    UniformDiscrete.rowKernel (computedOriginalHeadRootRow block hs m roots) =
      Submodule.comap (CompactOriginal.productOriginalHeadKernel block (computedOriginalHeadMask s m)).subtype
        (CompactOriginal.productOriginalDeletionKernel block
          (computedOriginalSelectedPhysicalDeletion block hs m roots)
          (productOriginalHeadDeletion s (computedOriginalHeadMask s m))) := by
  ext v
  rw [Submodule.mem_comap, computedOriginalSelectedPhysicalDeletion,
    CompactOriginal.productOriginalDeletionKernel_selectedPhysical,
    ← CompactOriginal.productOriginalHeadKernel_eq_deletionKernel, Submodule.mem_inf,
    UniformDiscrete.mem_ker_selectedRowMap]
  simp only [Submodule.subtype_apply, v.property, true_and, UniformDiscrete.mem_rowKernel]
  constructor
  · intro h x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact h i
  · intro h i
    exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The complete original deletion kernel is contained in the complete original retained head. -/
theorem computedOriginalSelectedKernel_le_head {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) (roots : computedOriginalWIndex s hs m → Fin s × ℤ) :
    CompactOriginal.productOriginalDeletionKernel block
      (computedOriginalSelectedPhysicalDeletion block hs m roots)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) ≤
        CompactOriginal.productOriginalHeadKernel block (computedOriginalHeadMask s m) := by
  rw [computedOriginalSelectedPhysicalDeletion, CompactOriginal.productOriginalDeletionKernel_selectedPhysical,
    ← CompactOriginal.productOriginalHeadKernel_eq_deletionKernel]
  exact inf_le_left

/-- The WHOLE selected row kernel and the WHOLE original support-deletion kernel are equivalent. -/
def computedOriginalSelectedKernelEquiv {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) (roots : computedOriginalWIndex s hs m → Fin s × ℤ) :
    UniformDiscrete.rowKernel (computedOriginalHeadRootRow block hs m roots) ≃ₗ[ℂ]
      CompactOriginal.productOriginalDeletionKernel block
        (computedOriginalSelectedPhysicalDeletion block hs m roots)
        (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) :=
  (LinearEquiv.ofEq _ _ (computedOriginalHeadRootKernel_eq_comap block hs m roots)).trans
    (Submodule.comapSubtypeEquivOfLe (computedOriginalSelectedKernel_le_head block hs m roots))

/-- A prescribed nonzero ENTIRE W determinant yields a COMPLETE actual strong pair line
for THIS finite deletion set, with the literal original corner normalized to one. -/
theorem computedOriginalSelectedRoot_complete_pair_line {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) (roots : computedOriginalWIndex s hs m → Fin s × ℤ)
    (hd : (computedOriginalWRootMatrix block hs m roots).det ≠ 0) :
    Module.finrank ℂ (CompactOriginal.productOriginalStrongDeletedPairSpace block
      (computedOriginalSelectedPhysicalDeletion block hs m roots)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m))) = 1 ∧
    ∃ r : productNumeratorIndex s → ℂ,
      r ∈ CompactOriginal.productOriginalDeletionKernel block
        (computedOriginalSelectedPhysicalDeletion block hs m roots)
        (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) ∧
      productCornerFunctional s r = 1 := by
  have hd' : (UniformDiscrete.originalCornerEvaluationMatrix (computedOriginalHeadRootRow block hs m roots)
      (computedOriginalHeadCornerFunctional block m) (computedOriginalHeadCornerBasis block hs m)).det ≠ 0 := by
    rw [computedOriginalHeadCornerEvaluationMatrix_eq]
    exact hd
  obtain ⟨hline, v, hv, hj⟩ := UniformDiscrete.originalCornerDeterminant_complete_line
    (computedOriginalHeadRootRow block hs m roots) (computedOriginalHeadCornerFunctional block m)
    (computedOriginalHeadCornerBasis block hs m) hd'
    (CompactOriginal.productOriginalHeadKernel_corner_ne_zero block hs (computedOriginalHeadMask s m))
  refine ⟨?_, v.val, ?_, hj⟩
  · rw [CompactOriginal.productOriginalStrongDeletedPairSpace_finrank_eq_kernel,
      ← (computedOriginalSelectedKernelEquiv block hs m roots).finrank_eq]
    exact hline
  · rw [computedOriginalHeadRootKernel_eq_comap] at hv
    exact hv

end

end MeyerGeneralProblem.StrongParity
