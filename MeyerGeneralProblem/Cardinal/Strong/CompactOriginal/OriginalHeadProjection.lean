module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadRank
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadTriangular
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadProjection

@[expose] public section

/-! Complete original OriginalHeadProjection for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

theorem productOriginalHeadRetainedPivot_ne_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (p : A) :
    productOriginalRetainedHeadRow block A p (productOriginalHeadPivotVector s hs A p) ≠ 0 :=
  productOriginalHeadRow_pivot_ne_zero block hs p.val

theorem productOriginalHeadRetained_cross_pivot_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (p q : A) (hpq : p ≠ q)
    (hd : productOriginalHeadRetainedDegree s A p ≤ productOriginalHeadRetainedDegree s A q) :
    productOriginalRetainedHeadRow block A p (productOriginalHeadPivotVector s hs A q) = 0 :=
  productOriginalHeadRow_cross_pivot_zero block hs p.val q.val
    (fun h => hpq (Subtype.ext h)) hd

/-- Definite finite elimination on the WHOLE original numerator slab. -/
def productOriginalHeadProjection {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] (productNumeratorIndex s → ℂ) :=
  UniformDiscrete.originalDegreeElimination (productOriginalRetainedHeadRow block A)
    (productOriginalHeadPivotVector s hs A) (productOriginalHeadRetainedDegree s A) (s + 1)

theorem productOriginalHeadProjection_mem_kernel {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (r : productNumeratorIndex s → ℂ) :
    productOriginalHeadProjection block hs A r ∈ productOriginalHeadKernel block A := by
  intro p
  exact UniformDiscrete.originalDegreeElimination_row_zero
    (productOriginalRetainedHeadRow block A) (productOriginalHeadPivotVector s hs A)
    (productOriginalHeadRetainedDegree s A) (productOriginalHeadRetainedPivot_ne_zero block hs A)
    (productOriginalHeadRetained_cross_pivot_zero block hs A) (s + 1) p
    (productOriginalHeadRetainedDegree_lt_steps s A p) r

theorem productOriginalHeadProjection_fixes_kernel {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (r : productNumeratorIndex s → ℂ)
    (hr : r ∈ productOriginalHeadKernel block A) :
    productOriginalHeadProjection block hs A r = r :=
  UniformDiscrete.originalDegreeElimination_fixes_rowKernel
    (productOriginalRetainedHeadRow block A) (productOriginalHeadPivotVector s hs A)
    (productOriginalHeadRetainedDegree s A) (s + 1) r hr

theorem productOriginalHeadProjection_pivot_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (p : A) :
    productOriginalHeadProjection block hs A (productOriginalHeadPivotVector s hs A p) = 0 :=
  UniformDiscrete.originalDegreeElimination_pivot_zero
    (productOriginalRetainedHeadRow block A) (productOriginalHeadPivotVector s hs A)
    (productOriginalHeadRetainedDegree s A) (productOriginalHeadRetainedPivot_ne_zero block hs A)
    (productOriginalHeadRetained_cross_pivot_zero block hs A) (s + 1) p
    (productOriginalHeadRetainedDegree_lt_steps s A p)

theorem productOriginalHeadProjection_free_coordinate {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (ij : productNumeratorIndex s)
    (hij : ∀ p : A, productOriginalHeadPivotIndex s hs p.val ≠ ij)
    (r : productNumeratorIndex s → ℂ) :
    productOriginalHeadProjection block hs A r ij = r ij := by
  classical
  have hh : ∀ p : A, (LinearMap.proj ij : (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ)
      (productOriginalHeadPivotVector s hs A p) = 0 := by
    intro p
    change productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs p.val) ij = 0
    simp only [productSlabCoordinateVector, Pi.single_apply]
    split_ifs with h
    · exact False.elim (hij p h.symm)
    · rfl
  exact UniformDiscrete.originalDegreeElimination_preserves_functional
    (productOriginalRetainedHeadRow block A) (productOriginalHeadPivotVector s hs A)
    (productOriginalHeadRetainedDegree s A) (s + 1) (LinearMap.proj ij) hh r

theorem productOriginalHeadProjection_idempotent {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (r : productNumeratorIndex s → ℂ) :
    productOriginalHeadProjection block hs A (productOriginalHeadProjection block hs A r) =
      productOriginalHeadProjection block hs A r :=
  productOriginalHeadProjection_fixes_kernel block hs A _
    (productOriginalHeadProjection_mem_kernel block hs A r)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
