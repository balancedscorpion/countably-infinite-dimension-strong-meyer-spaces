module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalWRootDeterminant

@[expose] public section

/-! Transfer the algebraic full-W nonzero determinant to the explicit ordinary
index family and the bijective labels of the COMPLETE native original carrier. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Some injective original-root tuple of the exact computed W size has nonzero
ENTIRE original physical-row determinant. No numeric rank oracle is assumed. -/
theorem computedOriginalWRootMatrix_det_ne_zero_exists {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) :
    ∃ roots : computedOriginalWIndex s hs m → Fin s × ℤ,
      Function.Injective roots ∧
        Matrix.det (computedOriginalWRootMatrix block hs m roots) ≠ 0 := by
  classical
  obtain ⟨E, e, _, hd⟩ := computedOriginalHeadCorner_specified_det_ne_zero block hs m
  let a := computedOriginalWIndexEquivActual block hs m
  let l := Equiv.ofBijective (compactOriginalRootPoint block) (compactOriginalRootPoint_bijective block)
  let roots : computedOriginalWIndex s hs m → Fin s × ℤ :=
    fun i => l.symm (e.symm (a i)).val
  have hx (i : computedOriginalWIndex s hs m) :
      compactOriginalRootPoint block (roots i) = (e.symm (a i)).val :=
    l.apply_symm_apply _
  refine ⟨roots, ?_, ?_⟩
  · intro i j hij
    apply a.injective
    apply e.symm.injective
    apply Subtype.val_injective
    exact (hx i).symm.trans ((congrArg (compactOriginalRootPoint block) hij).trans (hx j))
  · let A : Matrix (CompactOriginal.productOriginalHeadCornerFreeIndex block hs
        (computedOriginalHeadMask s m)) (CompactOriginal.productOriginalHeadCornerFreeIndex block hs
        (computedOriginalHeadMask s m)) ℂ :=
      fun i j => CompactOriginal.productOriginalHeadCornerPhysicalRow block (computedOriginalHeadMask s m)
        (e.symm i) (CompactOriginal.productOriginalHeadCornerFreeBasis block hs (computedOriginalHeadMask s m) j)
    have hA : A.det ≠ 0 := hd
    have heq : computedOriginalWRootMatrix block hs m roots =
        Matrix.reindex a.symm a.symm A := by
      rw [Matrix.reindex_apply]
      ext i j
      dsimp only [computedOriginalWRootMatrix, Matrix.submatrix, Equiv.symm_symm, A]
      have ha (k : computedOriginalWIndex s hs m) : computedOriginalWIndexToActual block hs m k = a k := rfl
      rw [hx, ha]
      rfl

    rw [heq, Matrix.det_reindex_self]
    exact hA

/-- The internally coupled block supplies all analytic inputs to full original-root rank. -/
theorem coupledComputedOriginalWRootMatrix_det_ne_zero_exists (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    ∃ roots : computedOriginalWIndex s hs m → Fin s × ℤ,
      Function.Injective roots ∧
        Matrix.det (coupledComputedOriginalWRootMatrix scales hpos offset s hs m roots) ≠ 0 :=
  computedOriginalWRootMatrix_det_ne_zero_exists
    (coupledCompactOriginalParameterBlock scales hpos offset s) hs m

end

end MeyerGeneralProblem.StrongParity
