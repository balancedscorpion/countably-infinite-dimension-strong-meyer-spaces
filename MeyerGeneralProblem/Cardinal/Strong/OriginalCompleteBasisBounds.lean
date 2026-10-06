module

public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalHeadBases
public import MeyerGeneralProblem.Cardinal.Strong.FiniteComplexPowers

@[expose] public section

/-! Computed integer norm bounds for the ENTIRE actual original H/W bases.
The full finite projection and corner correction are included. -/

namespace MeyerGeneralProblem.StrongParity

/-- Whole actual head projection size, obtained from the complete finite elimination. -/
def originalHeadProjectionSize (s : ℕ) (A : Finset (productOriginalHeadLabel s)) : ℕ :=
  coordinateEliminationSize (originalHeadMatrixSize s A) A.card
    (Fintype.card (productNumeratorIndex s)) (s + 1)

/-- Whole actual corner projection size, including every coordinate in the corner sum. -/
def originalHeadCornerProjectionSize (s : ℕ) (A : Finset (productOriginalHeadLabel s)) : ℕ :=
  (Fintype.card (productNumeratorIndex s) + 1) * originalHeadProjectionSize s A

noncomputable section

/-- Complete actual projected monomials obey the internally computed integer bound. -/
theorem compactOriginalHeadProjection_norm_le_size {s : ℕ}
    (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (j k : productNumeratorIndex s) :
    ‖CompactOriginal.productOriginalHeadProjection block hs A (productSlabCoordinateVector s j) k‖ ≤
      (originalHeadProjectionSize s A : ℝ) := by
  have h := complexCoordinateDegreeElimination_norm_le
    (fun head : A => fun l => CompactOriginal.productOriginalHeadRow block head.val
      (productSlabCoordinateVector s l))
    (fun head : A => rationalComplexValue (rationalOriginalHeadPivotInverse s head.val))
    (fun head : A => productOriginalHeadPivotIndex s hs head.val)
    (fun head : A => productOriginalHeadDegree s head.val) (originalHeadMatrixSize s A)
    (fun head l => compactOriginalHeadCoordinate_norm_le_matrix block A head l)
    (fun head => (rationalOriginalHeadPivotInverse_norm_one s head.val).le)
    (productSlabCoordinateVector s j)
    (by intro l; by_cases hl : l = j <;> simp [productSlabCoordinateVector, Pi.single_apply, hl])
    (s + 1) k
  rw [complexCoordinateDegreeElimination_eq_compact_headProjection] at h
  simpa only [originalHeadProjectionSize, Fintype.card_coe] using h

/-- Entire finite corner correction retains its computed size, including the full corner sum. -/
theorem originalCornerCorrection_norm_le_size (s : ℕ) (hs : 2 ≤ s)
    (v : productNumeratorIndex s → ℂ) (B : ℕ) (hv : ∀ k, ‖v k‖ ≤ (B : ℝ))
    (k : productNumeratorIndex s) :
    ‖v k - (∑ j : productNumeratorIndex s, v j) * productMiddleMonomial s hs k‖ ≤
      (((Fintype.card (productNumeratorIndex s) + 1) * B : ℕ) : ℝ) := by
  have hsum : ‖∑ j : productNumeratorIndex s, v j‖ ≤
      (Fintype.card (productNumeratorIndex s) : ℝ) * (B : ℝ) := by
    apply (norm_sum_le _ _).trans
    simpa using (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hv j))
  have hmul : ‖(∑ j : productNumeratorIndex s, v j) * productMiddleMonomial s hs k‖ ≤
      (Fintype.card (productNumeratorIndex s) : ℝ) * (B : ℝ) := by
    rw [norm_mul]
    exact (mul_le_mul hsum (productMiddleMonomial_coordinate_norm_le_one s hs k)
      (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  calc
    _ ≤ ‖v k‖ + ‖(∑ j : productNumeratorIndex s, v j) * productMiddleMonomial s hs k‖ := norm_sub_le _ _
    _ ≤ (B : ℝ) + (Fintype.card (productNumeratorIndex s) : ℝ) * (B : ℝ) := add_le_add (hv k) hmul
    _ = _ := by push_cast; ring

/-- EVERY coordinate of EVERY vector of the WHOLE H basis has a computed size bound. -/
theorem compactOriginalHeadFreeBasis_norm_le_size {s : ℕ}
    (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s) (A : Finset (productOriginalHeadLabel s))
    (j : productOriginalHeadFreeIndex s hs A) (k : productNumeratorIndex s) :
    ‖(CompactOriginal.productOriginalHeadFreeBasis block hs A j).val k‖ ≤
      (originalHeadProjectionSize s A : ℝ) := by
  rw [CompactOriginal.productOriginalHeadFreeBasis_vector]
  exact compactOriginalHeadProjection_norm_le_size block hs A j.val k

/-- EVERY coordinate of EVERY vector of the WHOLE W basis has its computed size bound. -/
theorem compactOriginalHeadCornerFreeBasis_norm_le_size {s : ℕ}
    (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s) (A : Finset (productOriginalHeadLabel s))
    (j : CompactOriginal.productOriginalHeadCornerFreeIndex block hs A) (k : productNumeratorIndex s) :
    ‖(CompactOriginal.productOriginalHeadCornerFreeBasis block hs A j).val.val k‖ ≤
      (originalHeadCornerProjectionSize s A : ℝ) := by
  have hv : (CompactOriginal.productOriginalHeadCornerFreeBasis block hs A j).val.val k =
      CompactOriginal.productOriginalHeadProjection block hs A (productSlabCoordinateVector s j.val.val) k -
      (∑ l : productNumeratorIndex s, CompactOriginal.productOriginalHeadProjection block hs A
        (productSlabCoordinateVector s j.val.val) l) * productMiddleMonomial s hs k := by
    rw [CompactOriginal.productOriginalHeadCornerFreeBasis_vector]
    simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [CompactOriginal.productOriginalHeadFreeBasis_middle,
      CompactOriginal.productOriginalHeadFreeBasis_vector]
    rfl
  rw [hv]
  exact originalCornerCorrection_norm_le_size s hs _ (originalHeadProjectionSize s A)
    (fun l => compactOriginalHeadProjection_norm_le_size block hs A j.val.val l) k

end

end MeyerGeneralProblem.StrongParity
