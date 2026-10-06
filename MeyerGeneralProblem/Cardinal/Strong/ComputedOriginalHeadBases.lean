module

public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalHeadMask
public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalHeadBasisNames
public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalCornerBasisNames

@[expose] public section

/-! Complete ordinary H/W basis programs with their forbidden original head
computed internally. The physical determinant search remains a separate step. -/

namespace MeyerGeneralProblem.StrongParity

/-- Complete original head projection program, with no supplied head mask. -/
def coupledCompactOriginalComputedHeadProjectionName (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (j : productNumeratorIndex s) (precision : ℕ) : productNumeratorIndex s → ℚ × ℚ :=
  coupledCompactOriginalHeadProjectionName scales hpos offset s hs
    (computedOriginalHeadMask s m) j precision

/-- Complete corner-corrected program with its whole forbidden head computed internally. -/
def coupledCompactOriginalComputedHeadCornerProjectionName (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (j : productNumeratorIndex s) (precision : ℕ) : productNumeratorIndex s → ℚ × ℚ :=
  coupledCompactOriginalHeadCornerProjectionName scales hpos offset s hs
    (computedOriginalHeadMask s m) j precision

noncomputable section

/-- The computed kernel imposes EVERY actual signed forbidden-head equation. -/
theorem mem_computedOriginalHeadKernel_geometric {s : ℕ}
    (block : CompactOriginalParameterBlock s) (m : ℕ) (hm : 0 < m)
    (v : productNumeratorIndex s → ℂ) :
    v ∈ CompactOriginal.productOriginalHeadKernel block (computedOriginalHeadMask s m) ↔
      ∀ label : spectralConeIndex,
        |originalPrivateSpectralLabelValue m label| ≤
          (((s / 2 : ℕ) : ℝ) / 2) / (parityDilationUnit * (m : ℝ)) →
        originalPrivateSpectralLabelValue m label ∉ originalSharedCoarseCone.carrier →
        CompactOriginal.productOriginalSpectralRow block (spectralConeIndexPoint label) v = 0 := by
  constructor
  · intro hv label hhead hcoarse
    have hh := (originalPrivateSpectralLabelValue_head_iff s m hm label).mp hhead
    let head : productOriginalHeadLabel s := ⟨label, hh⟩
    have hmem : head ∈ computedOriginalHeadMask s m :=
      (mem_computedOriginalHeadMask_geometric s m hm head).mpr hcoarse
    exact hv ⟨head, hmem⟩
  · intro hv head
    exact hv head.val.val
      ((originalPrivateSpectralLabelValue_head_iff s m hm head.val.val).mpr head.val.property)
      ((mem_computedOriginalHeadMask_geometric s m hm head.val).mp head.property)

/-- Exact dimension of the complete geometric head kernel, using the computed signed mask count. -/
theorem computedOriginalHeadKernel_finrank_add_card {s : ℕ}
    (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s) (m : ℕ) :
    Module.finrank ℂ (CompactOriginal.productOriginalHeadKernel block (computedOriginalHeadMask s m)) +
      (computedOriginalNoncoarseHeadLabels s m).card = (s + 1) ^ 2 - 1 := by
  rw [← computedOriginalHeadMask_card s m]
  exact CompactOriginal.productOriginalHeadKernel_finrank_add_card block hs _

/-- Exact size of the specified whole H basis, with the head list supplied internally. -/
theorem computedOriginalHeadFreeIndex_card {s : ℕ}
    (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s) (m : ℕ) :
    Fintype.card (productOriginalHeadFreeIndex s hs (computedOriginalHeadMask s m)) +
      (computedOriginalNoncoarseHeadLabels s m).card + 1 = (s + 1) ^ 2 := by
  rw [← computedOriginalHeadMask_card s m]
  exact CompactOriginal.productOriginalHeadFreeIndex_card block hs _

/-- Exact size of the specified whole W basis on the complete computed head. -/
theorem computedOriginalHeadCornerFreeIndex_card {s : ℕ}
    (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s) (m : ℕ) :
    Fintype.card (CompactOriginal.productOriginalHeadCornerFreeIndex block hs
      (computedOriginalHeadMask s m)) +
        (computedOriginalNoncoarseHeadLabels s m).card + 2 = (s + 1) ^ 2 := by
  rw [← computedOriginalHeadMask_card s m]
  exact CompactOriginal.productOriginalHeadCornerFreeIndex_card block hs _

/-- Algebraic nonzero original-root determinant on the ENTIRE internally masked W basis.
This supplies existence and exact size, without claiming the still-unimplemented search. -/
theorem computedOriginalHeadCorner_specified_det_ne_zero {s : ℕ}
    (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s) (m : ℕ) :
    ∃ E : Finset (compactOriginalProductSheetCarrier block).subtype,
      ∃ e : E ≃ CompactOriginal.productOriginalHeadCornerFreeIndex block hs (computedOriginalHeadMask s m),
        E.card + (computedOriginalNoncoarseHeadLabels s m).card + 2 = (s + 1) ^ 2 ∧
        Matrix.det (fun i j : CompactOriginal.productOriginalHeadCornerFreeIndex block hs
          (computedOriginalHeadMask s m) =>
            CompactOriginal.productOriginalHeadCornerPhysicalRow block (computedOriginalHeadMask s m)
              (e.symm i) (CompactOriginal.productOriginalHeadCornerFreeBasis block hs
                (computedOriginalHeadMask s m) j)) ≠ 0 := by
  rw [← computedOriginalHeadMask_card s m]
  exact CompactOriginal.productOriginalHeadCorner_specified_det_ne_zero block hs _

/-- Every vector of the complete actual H basis has the internally masked binary name. -/
theorem coupledCompactOriginalComputedHeadFreeBasisName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (j : productOriginalHeadFreeIndex s hs (computedOriginalHeadMask s m))
    (k : productNumeratorIndex s) (precision : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalComputedHeadProjectionName
      scales hpos offset s hs m j.val precision k) -
        (CompactOriginal.productOriginalHeadFreeBasis
          (coupledCompactOriginalParameterBlock scales hpos offset s) hs
            (computedOriginalHeadMask s m) j).val k‖ ≤ 1 / (2 : ℝ) ^ precision :=
  coupledCompactOriginalHeadFreeBasisName_error scales hpos offset s hs _ j k precision

/-- Every vector of the complete actual W basis has its internally masked binary name. -/
theorem coupledCompactOriginalComputedHeadCornerFreeBasisName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (j : CompactOriginal.productOriginalHeadCornerFreeIndex
      (coupledCompactOriginalParameterBlock scales hpos offset s) hs (computedOriginalHeadMask s m))
    (k : productNumeratorIndex s) (precision : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalComputedHeadCornerProjectionName
      scales hpos offset s hs m j.val.val precision k) -
        (CompactOriginal.productOriginalHeadCornerFreeBasis
          (coupledCompactOriginalParameterBlock scales hpos offset s) hs
            (computedOriginalHeadMask s m) j).val.val k‖ ≤ 1 / (2 : ℝ) ^ precision :=
  coupledCompactOriginalHeadCornerFreeBasisName_error scales hpos offset s hs _ j k precision

end

end MeyerGeneralProblem.StrongParity
