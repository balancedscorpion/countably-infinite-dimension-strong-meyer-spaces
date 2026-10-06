module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadProjection
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadRank
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadFreeBasis

@[expose] public section

/-! Complete original OriginalHeadFreeBasis for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The WHOLE head kernel, with explicit forward coordinate restriction and
inverse zero-padding followed by original degree elimination. -/
def productOriginalHeadFreeEquiv {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    productOriginalHeadKernel block A ≃ₗ[ℂ] (productOriginalHeadFreeIndex s hs A → ℂ) := by
  classical
  exact UniformDiscrete.originalFreeKernelEquiv (K := ℂ) (J := productNumeratorIndex s)
    (productOriginalRetainedHeadRow block A)
    (fun p : A => productOriginalHeadPivotIndex s hs p.val)
    (productOriginalHeadProjection block hs A)
    (productOriginalHeadProjection_mem_kernel block hs A)
    (productOriginalHeadProjection_fixes_kernel block hs A)
    (fun p => productOriginalHeadProjection_pivot_zero block hs A p)
    (fun r j => productOriginalHeadProjection_free_coordinate block hs A j.val
      (fun p h => j.property ⟨p, h⟩) r)

theorem productOriginalHeadFreeEquiv_apply {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (r : productOriginalHeadKernel block A)
    (j : productOriginalHeadFreeIndex s hs A) :
    productOriginalHeadFreeEquiv block hs A r j = r.val j.val := rfl

/-- The definite original free-monomial basis, after actual degree elimination. -/
def productOriginalHeadFreeBasis {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.Basis (productOriginalHeadFreeIndex s hs A) ℂ (productOriginalHeadKernel block A) :=
  (Pi.basisFun ℂ (productOriginalHeadFreeIndex s hs A)).map
    (productOriginalHeadFreeEquiv block hs A).symm

theorem productOriginalHeadFreeBasis_vector {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (j : productOriginalHeadFreeIndex s hs A) :
    (productOriginalHeadFreeBasis block hs A j : productNumeratorIndex s → ℂ) =
      productOriginalHeadProjection block hs A (productSlabCoordinateVector s j.val) := by
  classical
  rw [productOriginalHeadFreeBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change productOriginalHeadProjection block hs A
    (UniformDiscrete.originalFreeExtend
      (fun p : A => productOriginalHeadPivotIndex s hs p.val) (Pi.single j 1)) = _
  apply congrArg (productOriginalHeadProjection block hs A)
  exact UniformDiscrete.originalFreeExtend_single (K := ℂ) (J := productNumeratorIndex s)
    (fun p : A => productOriginalHeadPivotIndex s hs p.val) j

theorem productOriginalHeadFreeIndex_card {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Fintype.card (productOriginalHeadFreeIndex s hs A) + A.card + 1 = (s + 1) ^ 2 := by
  have hcard := Module.finrank_eq_card_basis (productOriginalHeadFreeBasis block hs A)
  have hH := productOriginalHeadKernel_finrank_add_card block hs A
  have hbox : 1 ≤ (s + 1) ^ 2 := by nlinarith
  omega

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
