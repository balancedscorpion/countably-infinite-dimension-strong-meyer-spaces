module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadFreeBasis
public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadGapBasis
public import MeyerGeneralProblem.UniformDiscrete.SpecifiedCornerBasis

@[expose] public section

/-! A definite basis of the WHOLE original head/corner kernel. The actual
middle monomial is an original free basis vector of corner one. Every other
free head vector is corrected by its literal original corner multiple. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The ACTUAL middle monomial coordinate, proved outside every original pivot. -/
def productOriginalHeadMiddleFreeIndex (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) : productOriginalHeadFreeIndex s hs A := by
  refine ⟨productInteriorIndex s (s / 2) (by omega), ?_⟩
  rintro ⟨p, hp⟩
  change productOriginalHeadPivotIndex s hs p.val = productInteriorIndex s (s / 2) _ at hp
  have hd := productOriginalHeadRetainedPivot_ne_zero s hs A p
  apply hd
  change productOriginalRetainedHeadRow s A p
    (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs p.val)) = 0
  rw [hp]
  exact productMiddleMonomial_mem_originalHeadKernel s hs A p

theorem productOriginalHeadFreeBasis_middle (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    (productOriginalHeadFreeBasis s hs A (productOriginalHeadMiddleFreeIndex s hs A) :
      productNumeratorIndex s → ℂ) = productMiddleMonomial s hs := by
  rw [productOriginalHeadFreeBasis_vector]
  change productOriginalHeadProjection s hs A (productMiddleMonomial s hs) = _
  exact productOriginalHeadProjection_fixes_kernel s hs A _
    (productMiddleMonomial_mem_originalHeadKernel s hs A)

theorem productOriginalHeadFreeBasis_middle_corner (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    ((productCornerFunctional s).comp (productOriginalHeadKernel s A).subtype)
      (productOriginalHeadFreeBasis s hs A (productOriginalHeadMiddleFreeIndex s hs A)) = 1 := by
  change productCornerFunctional s
    (productOriginalHeadFreeBasis s hs A (productOriginalHeadMiddleFreeIndex s hs A) :
      productNumeratorIndex s → ℂ) = 1
  rw [productOriginalHeadFreeBasis_middle, productMiddleMonomial_corner]

/-- Every original free head coordinate except the ACTUAL middle monomial. -/
abbrev productOriginalHeadCornerFreeIndex (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :=
  UniformDiscrete.originalFreeIndex (fun _ : Unit => productOriginalHeadMiddleFreeIndex s hs A)

/-- The complete corner-zero kernel has explicit corrected free coordinates. -/
def productOriginalHeadCornerFreeEquiv (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    productOriginalHeadCornerKernel s A ≃ₗ[ℂ] (productOriginalHeadCornerFreeIndex s hs A → ℂ) := by
  classical
  exact UniformDiscrete.specifiedCornerFreeEquiv (K := ℂ)
    (V := productOriginalHeadKernel s A) (productOriginalHeadFreeBasis s hs A)
    ((productCornerFunctional s).comp (productOriginalHeadKernel s A).subtype)
    (productOriginalHeadMiddleFreeIndex s hs A) (productOriginalHeadFreeBasis_middle_corner s hs A)

/-- The literal corrected original monomial basis of the WHOLE head/corner kernel. -/
def productOriginalHeadCornerFreeBasis (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.Basis (productOriginalHeadCornerFreeIndex s hs A) ℂ (productOriginalHeadCornerKernel s A) :=
  (Pi.basisFun ℂ (productOriginalHeadCornerFreeIndex s hs A)).map
    (productOriginalHeadCornerFreeEquiv s hs A).symm

theorem productOriginalHeadCornerFreeBasis_vector (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (j : productOriginalHeadCornerFreeIndex s hs A) :
    (productOriginalHeadCornerFreeBasis s hs A j).val =
      productOriginalHeadFreeBasis s hs A j.val -
        productCornerFunctional s (productOriginalHeadFreeBasis s hs A j.val) •
          productOriginalHeadFreeBasis s hs A (productOriginalHeadMiddleFreeIndex s hs A) := by
  classical
  exact UniformDiscrete.specifiedCornerFreeBasis_vector (K := ℂ)
    (V := productOriginalHeadKernel s A) (productOriginalHeadFreeBasis s hs A)
    ((productCornerFunctional s).comp (productOriginalHeadKernel s A).subtype)
    (productOriginalHeadMiddleFreeIndex s hs A) (productOriginalHeadFreeBasis_middle_corner s hs A) j

theorem productOriginalHeadCornerFreeIndex_card (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Fintype.card (productOriginalHeadCornerFreeIndex s hs A) + A.card + 2 = (s + 1) ^ 2 := by
  have hcard := Module.finrank_eq_card_basis (productOriginalHeadCornerFreeBasis s hs A)
  have hW := productOriginalHeadKernel_corner_kernel_finrank_add_one s hs A
  change Module.finrank ℂ (productOriginalHeadCornerKernel s A) + 1 =
    Module.finrank ℂ (productOriginalHeadKernel s A) at hW
  have hH := productOriginalHeadKernel_finrank_add_card s hs A
  have hbox : 1 ≤ (s + 1) ^ 2 := by nlinarith
  omega

/-- A nonzero ORIGINAL root determinant on THIS definite complete original
head/corner basis, of its proved exact known size. Root computations and
certified interval search remain separate analytic implementation obligations. -/
theorem productOriginalHeadCorner_specified_det_ne_zero (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    ∃ E : Finset (productSheetCarrier s).subtype,
      ∃ e : E ≃ productOriginalHeadCornerFreeIndex s hs A,
        E.card + A.card + 2 = (s + 1) ^ 2 ∧
        Matrix.det (fun i j : productOriginalHeadCornerFreeIndex s hs A =>
          productOriginalHeadCornerPhysicalRow s A (e.symm i)
            (productOriginalHeadCornerFreeBasis s hs A j)) ≠ 0 := by
  classical
  exact productOriginalHeadCorner_original_det_ne_zero s hs A
    (J := productOriginalHeadCornerFreeIndex s hs A) (productOriginalHeadCornerFreeBasis s hs A)

end

end MeyerGeneralProblem.StrongParity
