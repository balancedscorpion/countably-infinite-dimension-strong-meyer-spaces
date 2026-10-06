module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadProjection
public import MeyerGeneralProblem.UniformDiscrete.OriginalFreeKernelBasis

@[expose] public section

/-! An explicit basis of the COMPLETE original head kernel: eliminate the
original free monomials by the literal finite degree projection. No arbitrary
kernel basis, missing signed coefficient rows or unknown rank test is used. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Original slab coordinates outside ALL retained original head pivots. -/
abbrev productOriginalHeadFreeIndex (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :=
  UniformDiscrete.originalFreeIndex (fun p : A => productOriginalHeadPivotIndex s hs p.val)

/-- Free index equality is decided on the underlying finite ORIGINAL coordinates. -/
instance productOriginalHeadFreeIndex_decidableEq (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) : DecidableEq (productOriginalHeadFreeIndex s hs A) := by
  unfold productOriginalHeadFreeIndex UniformDiscrete.originalFreeIndex productNumeratorIndex
  infer_instance

/-- The WHOLE head kernel, with explicit forward coordinate restriction and
inverse zero-padding followed by original degree elimination. -/
def productOriginalHeadFreeEquiv (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    productOriginalHeadKernel s A ≃ₗ[ℂ] (productOriginalHeadFreeIndex s hs A → ℂ) := by
  classical
  exact UniformDiscrete.originalFreeKernelEquiv (K := ℂ) (J := productNumeratorIndex s)
    (productOriginalRetainedHeadRow s A)
    (fun p : A => productOriginalHeadPivotIndex s hs p.val)
    (productOriginalHeadProjection s hs A)
    (productOriginalHeadProjection_mem_kernel s hs A)
    (productOriginalHeadProjection_fixes_kernel s hs A)
    (fun p => productOriginalHeadProjection_pivot_zero s hs A p)
    (fun r j => productOriginalHeadProjection_free_coordinate s hs A j.val
      (fun p h => j.property ⟨p, h⟩) r)

theorem productOriginalHeadFreeEquiv_apply (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (r : productOriginalHeadKernel s A)
    (j : productOriginalHeadFreeIndex s hs A) :
    productOriginalHeadFreeEquiv s hs A r j = r.val j.val := rfl

/-- The definite original free-monomial basis, after actual degree elimination. -/
def productOriginalHeadFreeBasis (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.Basis (productOriginalHeadFreeIndex s hs A) ℂ (productOriginalHeadKernel s A) :=
  (Pi.basisFun ℂ (productOriginalHeadFreeIndex s hs A)).map
    (productOriginalHeadFreeEquiv s hs A).symm

theorem productOriginalHeadFreeBasis_vector (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (j : productOriginalHeadFreeIndex s hs A) :
    (productOriginalHeadFreeBasis s hs A j : productNumeratorIndex s → ℂ) =
      productOriginalHeadProjection s hs A (productSlabCoordinateVector s j.val) := by
  classical
  rw [productOriginalHeadFreeBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change productOriginalHeadProjection s hs A
    (UniformDiscrete.originalFreeExtend
      (fun p : A => productOriginalHeadPivotIndex s hs p.val) (Pi.single j 1)) = _
  apply congrArg (productOriginalHeadProjection s hs A)
  exact UniformDiscrete.originalFreeExtend_single (K := ℂ) (J := productNumeratorIndex s)
    (fun p : A => productOriginalHeadPivotIndex s hs p.val) j

theorem productOriginalHeadFreeIndex_card (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Fintype.card (productOriginalHeadFreeIndex s hs A) + A.card + 1 = (s + 1) ^ 2 := by
  have hcard := Module.finrank_eq_card_basis (productOriginalHeadFreeBasis s hs A)
  have hH := productOriginalHeadKernel_finrank_add_card s hs A
  have hbox : 1 ≤ (s + 1) ^ 2 := by nlinarith
  omega

end

end MeyerGeneralProblem.StrongParity
