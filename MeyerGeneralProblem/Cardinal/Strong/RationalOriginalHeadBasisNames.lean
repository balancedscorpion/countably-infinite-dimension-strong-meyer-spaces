module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalHeadProjection

@[expose] public section

/-! Implemented ordinary binary names for EVERY vector of the COMPLETE original
head basis on coupled compact blocks. The finite entry and elimination error
budgets are computed from the whole retained head and numerator families. -/

namespace MeyerGeneralProblem.StrongParity

/-- Complete rational projection with entry precision q has its computed sensitivity bound. -/
theorem coupledCompactOriginalHeadProjectionAt_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (j k : productNumeratorIndex s) (precision : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalHeadProjectionAt scales hpos offset s hs A j precision k) -
      CompactOriginal.productOriginalHeadProjection (coupledCompactOriginalParameterBlock scales hpos offset s)
        hs A (productSlabCoordinateVector s j) k‖ ≤
      (originalHeadProjectionSensitivity s A : ℝ) * (1 / (2 : ℝ) ^ precision) := by
  rw [coupledCompactOriginalHeadProjectionAt, rationalComplexDegreeElimination_value]
  have hv : (fun l => rationalComplexValue (rationalOriginalMonomial s j l)) =
      productSlabCoordinateVector s j := funext (rationalOriginalMonomial_value s j)
  rw [hv]
  have h := complexCoordinateDegreeElimination_sub_norm_le
    (fun head : A => fun l => rationalComplexValue
      (coupledCompactOriginalSpectralCoordinateName scales hpos offset s l head.val.val precision))
    (fun head : A => fun l => CompactOriginal.productOriginalHeadRow
      (coupledCompactOriginalParameterBlock scales hpos offset s) head.val (productSlabCoordinateVector s l))
    (fun head : A => rationalComplexValue (rationalOriginalHeadPivotInverse s head.val))
    (fun head : A => productOriginalHeadPivotIndex s hs head.val)
    (fun head : A => productOriginalHeadDegree s head.val) (originalHeadMatrixSize s A)
    (fun head l => coupledCompactOriginalHeadCoordinateName_norm_le_matrix scales hpos offset s A head l precision)
    (fun head l => compactOriginalHeadCoordinate_norm_le_matrix _ A head l)
    (fun head => (rationalOriginalHeadPivotInverse_norm_one s head.val).le)
    (1 / (2 : ℝ) ^ precision) (by positivity)
    (fun head l => coupledCompactOriginalHeadCoordinateName_error scales hpos offset s l head.val precision)
    (productSlabCoordinateVector s j)
    (by intro l; by_cases hl : l = j <;> simp [productSlabCoordinateVector, Pi.single_apply, hl])
    (s + 1) k
  rw [complexCoordinateDegreeElimination_eq_compact_headProjection] at h
  simpa only [originalHeadProjectionSensitivity, Fintype.card_coe] using h

/-- Internally budgeted binary approximation to every coordinate of the complete head projection. -/
theorem coupledCompactOriginalHeadProjectionName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (j k : productNumeratorIndex s) (precision : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalHeadProjectionName scales hpos offset s hs A j precision k) -
      CompactOriginal.productOriginalHeadProjection (coupledCompactOriginalParameterBlock scales hpos offset s)
        hs A (productSlabCoordinateVector s j) k‖ ≤ 1 / (2 : ℝ) ^ precision :=
  (coupledCompactOriginalHeadProjectionAt_error scales hpos offset s hs A j k
    (precision + originalHeadProjectionSensitivity s A)).trans
      (integer_sensitivity_binary_shift (originalHeadProjectionSensitivity s A) precision)

/-- ALL vectors in the specified basis of the WHOLE original H space have ordinary binary names. -/
theorem coupledCompactOriginalHeadFreeBasisName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (j : productOriginalHeadFreeIndex s hs A)
    (k : productNumeratorIndex s) (precision : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalHeadProjectionName scales hpos offset s hs A j.val precision k) -
      (CompactOriginal.productOriginalHeadFreeBasis (coupledCompactOriginalParameterBlock scales hpos offset s)
        hs A j).val k‖ ≤ 1 / (2 : ℝ) ^ precision := by
  rw [CompactOriginal.productOriginalHeadFreeBasis_vector]
  exact coupledCompactOriginalHeadProjectionName_error scales hpos offset s hs A j.val k precision

end MeyerGeneralProblem.StrongParity
