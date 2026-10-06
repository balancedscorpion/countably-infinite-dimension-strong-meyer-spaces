module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadRank
public import MeyerGeneralProblem.UniformDiscrete.OriginalTriangularProjection

@[expose] public section

/-! The literal finite original head projection. Its pivots are the actual
low/high numerator monomials, retaining both quarter-phased signs and ANY
retained head subset. Exactly `s+1` degree steps suffice on the whole kernel. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- ORIGINAL monomial pivot vectors for every retained original head row. -/
def productOriginalHeadPivotVector (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (p : A) : productNumeratorIndex s → ℂ :=
  productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs p.val)

/-- The literal degree of each retained original head row. -/
def productOriginalHeadRetainedDegree (s : ℕ) (A : Finset (productOriginalHeadLabel s))
    (p : A) : ℕ := productOriginalHeadDegree s p.val

theorem productOriginalHeadRetainedPivot_ne_zero (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (p : A) :
    productOriginalRetainedHeadRow s A p (productOriginalHeadPivotVector s hs A p) ≠ 0 :=
  productOriginalHeadRow_pivot_ne_zero s hs p.val

theorem productOriginalHeadRetained_cross_pivot_zero (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (p q : A) (hpq : p ≠ q)
    (hd : productOriginalHeadRetainedDegree s A p ≤ productOriginalHeadRetainedDegree s A q) :
    productOriginalRetainedHeadRow s A p (productOriginalHeadPivotVector s hs A q) = 0 :=
  productOriginalHeadRow_cross_pivot_zero s hs p.val q.val
    (fun h => hpq (Subtype.ext h)) hd

theorem productOriginalHeadRetainedDegree_le_half (s : ℕ)
    (A : Finset (productOriginalHeadLabel s)) (p : A) :
    productOriginalHeadRetainedDegree s A p ≤ s / 2 := by
  have hb := productOriginalHeadCoordinates_bound s p.val
  have hr : (productOriginalHeadRetainedDegree s A p : ℝ) ≤ ((s / 2 : ℕ) : ℝ) := by
    change (((spectralConeIndexCoordinates p.val.val).1 +
      (spectralConeIndexCoordinates p.val.val).2 : ℕ) : ℝ) ≤ ((s / 2 : ℕ) : ℝ)
    push_cast
    linarith
  exact_mod_cast hr

theorem productOriginalHeadRetainedDegree_lt_steps (s : ℕ)
    (A : Finset (productOriginalHeadLabel s)) (p : A) :
    productOriginalHeadRetainedDegree s A p < s + 1 :=
  Nat.lt_succ_of_le ((productOriginalHeadRetainedDegree_le_half s A p).trans
    (Nat.div_le_self s 2))

/-- Definite finite elimination on the WHOLE original numerator slab. -/
def productOriginalHeadProjection (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] (productNumeratorIndex s → ℂ) :=
  UniformDiscrete.originalDegreeElimination (productOriginalRetainedHeadRow s A)
    (productOriginalHeadPivotVector s hs A) (productOriginalHeadRetainedDegree s A) (s + 1)

theorem productOriginalHeadProjection_mem_kernel (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (r : productNumeratorIndex s → ℂ) :
    productOriginalHeadProjection s hs A r ∈ productOriginalHeadKernel s A := by
  intro p
  exact UniformDiscrete.originalDegreeElimination_row_zero
    (productOriginalRetainedHeadRow s A) (productOriginalHeadPivotVector s hs A)
    (productOriginalHeadRetainedDegree s A) (productOriginalHeadRetainedPivot_ne_zero s hs A)
    (productOriginalHeadRetained_cross_pivot_zero s hs A) (s + 1) p
    (productOriginalHeadRetainedDegree_lt_steps s A p) r

theorem productOriginalHeadProjection_fixes_kernel (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (r : productNumeratorIndex s → ℂ)
    (hr : r ∈ productOriginalHeadKernel s A) :
    productOriginalHeadProjection s hs A r = r :=
  UniformDiscrete.originalDegreeElimination_fixes_rowKernel
    (productOriginalRetainedHeadRow s A) (productOriginalHeadPivotVector s hs A)
    (productOriginalHeadRetainedDegree s A) (s + 1) r hr

theorem productOriginalHeadProjection_pivot_zero (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (p : A) :
    productOriginalHeadProjection s hs A (productOriginalHeadPivotVector s hs A p) = 0 :=
  UniformDiscrete.originalDegreeElimination_pivot_zero
    (productOriginalRetainedHeadRow s A) (productOriginalHeadPivotVector s hs A)
    (productOriginalHeadRetainedDegree s A) (productOriginalHeadRetainedPivot_ne_zero s hs A)
    (productOriginalHeadRetained_cross_pivot_zero s hs A) (s + 1) p
    (productOriginalHeadRetainedDegree_lt_steps s A p)

theorem productOriginalHeadProjection_free_coordinate (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (ij : productNumeratorIndex s)
    (hij : ∀ p : A, productOriginalHeadPivotIndex s hs p.val ≠ ij)
    (r : productNumeratorIndex s → ℂ) :
    productOriginalHeadProjection s hs A r ij = r ij := by
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
    (productOriginalRetainedHeadRow s A) (productOriginalHeadPivotVector s hs A)
    (productOriginalHeadRetainedDegree s A) (s + 1) (LinearMap.proj ij) hh r

theorem productOriginalHeadProjection_idempotent (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (r : productNumeratorIndex s → ℂ) :
    productOriginalHeadProjection s hs A (productOriginalHeadProjection s hs A r) =
      productOriginalHeadProjection s hs A r :=
  productOriginalHeadProjection_fixes_kernel s hs A _
    (productOriginalHeadProjection_mem_kernel s hs A r)

end

end MeyerGeneralProblem.StrongParity
