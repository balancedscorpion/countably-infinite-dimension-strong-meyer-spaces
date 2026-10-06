module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadFreeBasis
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadGapBasis
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadProjection
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadRank
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadCornerBasis

@[expose] public section

/-! Complete original OriginalHeadCornerBasis for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The ACTUAL middle monomial coordinate, proved outside every original pivot. -/
def productOriginalHeadMiddleFreeIndex {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) : productOriginalHeadFreeIndex s hs A := by
  refine ⟨productInteriorIndex s (s / 2) (by omega), ?_⟩
  rintro ⟨p, hp⟩
  change productOriginalHeadPivotIndex s hs p.val = productInteriorIndex s (s / 2) _ at hp
  have hd := productOriginalHeadRetainedPivot_ne_zero block hs A p
  apply hd
  change productOriginalRetainedHeadRow block A p
    (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs p.val)) = 0
  rw [hp]
  exact productMiddleMonomial_mem_originalHeadKernel block hs A p

theorem productOriginalHeadFreeBasis_middle {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    (productOriginalHeadFreeBasis block hs A (productOriginalHeadMiddleFreeIndex block hs A) :
      productNumeratorIndex s → ℂ) = productMiddleMonomial s hs := by
  rw [productOriginalHeadFreeBasis_vector]
  change productOriginalHeadProjection block hs A (productMiddleMonomial s hs) = _
  exact productOriginalHeadProjection_fixes_kernel block hs A _
    (productMiddleMonomial_mem_originalHeadKernel block hs A)

theorem productOriginalHeadFreeBasis_middle_corner {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    ((productCornerFunctional s).comp (productOriginalHeadKernel block A).subtype)
      (productOriginalHeadFreeBasis block hs A (productOriginalHeadMiddleFreeIndex block hs A)) = 1 := by
  change productCornerFunctional s
    (productOriginalHeadFreeBasis block hs A (productOriginalHeadMiddleFreeIndex block hs A) :
      productNumeratorIndex s → ℂ) = 1
  rw [productOriginalHeadFreeBasis_middle, productMiddleMonomial_corner]

/-- Every original free head coordinate except the ACTUAL middle monomial. -/
abbrev productOriginalHeadCornerFreeIndex {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :=
  UniformDiscrete.originalFreeIndex (fun _ : Unit => productOriginalHeadMiddleFreeIndex block hs A)

/-- The complete corner-zero kernel has explicit corrected free coordinates. -/
def productOriginalHeadCornerFreeEquiv {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    productOriginalHeadCornerKernel block A ≃ₗ[ℂ] (productOriginalHeadCornerFreeIndex block hs A → ℂ) := by
  classical
  exact UniformDiscrete.specifiedCornerFreeEquiv (K := ℂ)
    (V := productOriginalHeadKernel block A) (productOriginalHeadFreeBasis block hs A)
    ((productCornerFunctional s).comp (productOriginalHeadKernel block A).subtype)
    (productOriginalHeadMiddleFreeIndex block hs A) (productOriginalHeadFreeBasis_middle_corner block hs A)

/-- The literal corrected original monomial basis of the WHOLE head/corner kernel. -/
def productOriginalHeadCornerFreeBasis {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.Basis (productOriginalHeadCornerFreeIndex block hs A) ℂ (productOriginalHeadCornerKernel block A) :=
  (Pi.basisFun ℂ (productOriginalHeadCornerFreeIndex block hs A)).map
    (productOriginalHeadCornerFreeEquiv block hs A).symm

theorem productOriginalHeadCornerFreeBasis_vector {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (j : productOriginalHeadCornerFreeIndex block hs A) :
    (productOriginalHeadCornerFreeBasis block hs A j).val =
      productOriginalHeadFreeBasis block hs A j.val -
        productCornerFunctional s (productOriginalHeadFreeBasis block hs A j.val) •
          productOriginalHeadFreeBasis block hs A (productOriginalHeadMiddleFreeIndex block hs A) := by
  classical
  exact UniformDiscrete.specifiedCornerFreeBasis_vector (K := ℂ)
    (V := productOriginalHeadKernel block A) (productOriginalHeadFreeBasis block hs A)
    ((productCornerFunctional s).comp (productOriginalHeadKernel block A).subtype)
    (productOriginalHeadMiddleFreeIndex block hs A) (productOriginalHeadFreeBasis_middle_corner block hs A) j

theorem productOriginalHeadCornerFreeIndex_card {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Fintype.card (productOriginalHeadCornerFreeIndex block hs A) + A.card + 2 = (s + 1) ^ 2 := by
  have hcard := Module.finrank_eq_card_basis (productOriginalHeadCornerFreeBasis block hs A)
  have hW := productOriginalHeadKernel_corner_kernel_finrank_add_one block hs A
  change Module.finrank ℂ (productOriginalHeadCornerKernel block A) + 1 =
    Module.finrank ℂ (productOriginalHeadKernel block A) at hW
  have hH := productOriginalHeadKernel_finrank_add_card block hs A
  have hbox : 1 ≤ (s + 1) ^ 2 := by nlinarith
  omega

/-- A nonzero ORIGINAL root determinant on THIS definite complete original
head/corner basis, of its proved exact known size. Root computations and
certified interval search remain separate analytic implementation obligations. -/
theorem productOriginalHeadCorner_specified_det_ne_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    ∃ E : Finset (compactOriginalProductSheetCarrier block).subtype,
      ∃ e : E ≃ productOriginalHeadCornerFreeIndex block hs A,
        E.card + A.card + 2 = (s + 1) ^ 2 ∧
        Matrix.det (fun i j : productOriginalHeadCornerFreeIndex block hs A =>
          productOriginalHeadCornerPhysicalRow block A (e.symm i)
            (productOriginalHeadCornerFreeBasis block hs A j)) ≠ 0 := by
  classical
  exact productOriginalHeadCorner_original_det_ne_zero block hs A
    (J := productOriginalHeadCornerFreeIndex block hs A) (productOriginalHeadCornerFreeBasis block hs A)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
