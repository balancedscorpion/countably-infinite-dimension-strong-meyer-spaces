module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalCornerCorrection

@[expose] public section

/-! Implemented ordinary binary names for ALL vectors of the specified complete
original head/corner basis. Both finite elimination and the complete corner sum
are included in the internally computed precision budget. -/

namespace MeyerGeneralProblem.StrongParity

/-- Sensitivity of the full original head projection followed by corner correction. -/
def originalHeadCornerProjectionSensitivity (s : ℕ) (A : Finset (productOriginalHeadLabel s)) : ℕ :=
  (Fintype.card (productNumeratorIndex s) + 1) * originalHeadProjectionSensitivity s A

/-- Ordinary rational name of the entire original corner-corrected projected monomial. -/
def coupledCompactOriginalHeadCornerProjectionName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (A : Finset (productOriginalHeadLabel s))
    (j : productNumeratorIndex s) (precision : ℕ) : productNumeratorIndex s → ℚ × ℚ :=
  rationalOriginalCornerCorrection s hs
    (coupledCompactOriginalHeadProjectionAt scales hpos offset s hs A j
      (precision + originalHeadCornerProjectionSensitivity s A))

/-- Every corrected projected monomial coordinate has its internally budgeted binary error. -/
theorem coupledCompactOriginalHeadCornerProjectionName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (j k : productNumeratorIndex s) (precision : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalHeadCornerProjectionName scales hpos offset s hs A j precision k) -
      (CompactOriginal.productOriginalHeadProjection (coupledCompactOriginalParameterBlock scales hpos offset s)
        hs A (productSlabCoordinateVector s j) k -
        (∑ l : productNumeratorIndex s, CompactOriginal.productOriginalHeadProjection
          (coupledCompactOriginalParameterBlock scales hpos offset s) hs A (productSlabCoordinateVector s j) l) *
        productMiddleMonomial s hs k)‖ ≤ 1 / (2 : ℝ) ^ precision := by
  rw [coupledCompactOriginalHeadCornerProjectionName, rationalOriginalCornerCorrection_value]
  have h := originalCornerCorrection_sub_norm_le s hs
    (fun l => rationalComplexValue (coupledCompactOriginalHeadProjectionAt scales hpos offset s hs A j
      (precision + originalHeadCornerProjectionSensitivity s A) l))
    (CompactOriginal.productOriginalHeadProjection (coupledCompactOriginalParameterBlock scales hpos offset s)
      hs A (productSlabCoordinateVector s j))
    (originalHeadProjectionSensitivity s A)
    (1 / (2 : ℝ) ^ (precision + originalHeadCornerProjectionSensitivity s A))
    (fun l => coupledCompactOriginalHeadProjectionAt_error scales hpos offset s hs A j l
      (precision + originalHeadCornerProjectionSensitivity s A)) k
  exact h.trans (integer_sensitivity_binary_shift (originalHeadCornerProjectionSensitivity s A) precision)

/-- ALL vectors in the specified basis of the WHOLE original W space have ordinary binary names. -/
theorem coupledCompactOriginalHeadCornerFreeBasisName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s))
    (j : CompactOriginal.productOriginalHeadCornerFreeIndex
      (coupledCompactOriginalParameterBlock scales hpos offset s) hs A)
    (k : productNumeratorIndex s) (precision : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalHeadCornerProjectionName scales hpos offset s hs A j.val.val precision k) -
      (CompactOriginal.productOriginalHeadCornerFreeBasis (coupledCompactOriginalParameterBlock scales hpos offset s)
        hs A j).val.val k‖ ≤ 1 / (2 : ℝ) ^ precision := by
  have hv : (CompactOriginal.productOriginalHeadCornerFreeBasis
      (coupledCompactOriginalParameterBlock scales hpos offset s) hs A j).val.val k =
      CompactOriginal.productOriginalHeadProjection (coupledCompactOriginalParameterBlock scales hpos offset s)
        hs A (productSlabCoordinateVector s j.val.val) k -
      (∑ l : productNumeratorIndex s, CompactOriginal.productOriginalHeadProjection
        (coupledCompactOriginalParameterBlock scales hpos offset s) hs A (productSlabCoordinateVector s j.val.val) l) *
        productMiddleMonomial s hs k := by
    rw [CompactOriginal.productOriginalHeadCornerFreeBasis_vector]
    simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [CompactOriginal.productOriginalHeadFreeBasis_middle]
    rw [CompactOriginal.productOriginalHeadFreeBasis_vector]
    rfl
  rw [hv]
  exact coupledCompactOriginalHeadCornerProjectionName_error scales hpos offset s hs A j.val.val k precision

end MeyerGeneralProblem.StrongParity
