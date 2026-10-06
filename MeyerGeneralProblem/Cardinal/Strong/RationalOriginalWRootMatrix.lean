module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalWRootRows
public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalWIndices
public import MeyerGeneralProblem.Cardinal.Strong.FiniteComplexDeterminantBounds

@[expose] public section

/-! Ordinary full original-root matrices on the explicit computed index family
of the WHOLE W basis. No classical finite enumeration enters the matrix program. -/

namespace MeyerGeneralProblem.StrongParity

/-- Pure proof lift from the explicit W list into the internally constructed coupled basis type. -/
def coupledComputedOriginalWIndexToActual (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (k : computedOriginalWIndex s hs m) :
    CompactOriginal.productOriginalHeadCornerFreeIndex
      (coupledCompactOriginalParameterBlock scales hpos offset s) hs (computedOriginalHeadMask s m) :=
  ⟨⟨k.val, (computedOriginalWIndexToActual
    (coupledCompactOriginalParameterBlock scales hpos offset s) hs m k).val.property⟩,
    (computedOriginalWIndexToActual (coupledCompactOriginalParameterBlock scales hpos offset s) hs m k).property⟩

/-- Ordinary complete matrix program on every root tuple of the proved exact W size. -/
def coupledComputedOriginalWRootMatrixName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (roots : computedOriginalWIndex s hs m → Fin s × ℤ) (p : ℕ) :
    Matrix (computedOriginalWIndex s hs m) (computedOriginalWIndex s hs m) (ℚ × ℚ) :=
  fun i j => coupledCompactOriginalWRootRowName scales hpos offset s hs m (roots i).1 (roots i).2
    (coupledComputedOriginalWIndexToActual scales hpos offset s hs m j) p

noncomputable section

/-- The computed proof lift is exactly the original full-basis index equivalence. -/
theorem coupledComputedOriginalWIndexToActual_eq (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (k : computedOriginalWIndex s hs m) :
    coupledComputedOriginalWIndexToActual scales hpos offset s hs m k =
      computedOriginalWIndexToActual (coupledCompactOriginalParameterBlock scales hpos offset s) hs m k :=
  Subtype.ext (Subtype.ext rfl)

/-- The actual entire original physical-row matrix on the ENTIRE specified W basis. -/
def computedOriginalWRootMatrix {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ)
    (roots : computedOriginalWIndex s hs m → Fin s × ℤ) :
    Matrix (computedOriginalWIndex s hs m) (computedOriginalWIndex s hs m) ℂ :=
  fun i j => CompactOriginal.productOriginalHeadCornerPhysicalRow block (computedOriginalHeadMask s m)
    (compactOriginalRootPoint block (roots i))
    (CompactOriginal.productOriginalHeadCornerFreeBasis block hs (computedOriginalHeadMask s m)
      (computedOriginalWIndexToActual block hs m j))

/-- Actual full original matrix for the internally supplied coupled parameter block. -/
def coupledComputedOriginalWRootMatrix (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (roots : computedOriginalWIndex s hs m → Fin s × ℤ) :
    Matrix (computedOriginalWIndex s hs m) (computedOriginalWIndex s hs m) ℂ :=
  computedOriginalWRootMatrix (coupledCompactOriginalParameterBlock scales hpos offset s) hs m roots

/-- Every entry of every complete computed original root matrix has its requested binary error. -/
theorem coupledComputedOriginalWRootMatrixName_entry_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (roots : computedOriginalWIndex s hs m → Fin s × ℤ) (p : ℕ)
    (i j : computedOriginalWIndex s hs m) :
    ‖rationalComplexValue (coupledComputedOriginalWRootMatrixName scales hpos offset s hs m roots p i j) -
      coupledComputedOriginalWRootMatrix scales hpos offset s hs m roots i j‖ ≤ 1 / (2 : ℝ) ^ p := by
  have h := coupledCompactOriginalWRootRowName_error scales hpos offset s hs m (roots i).1 (roots i).2
    (coupledComputedOriginalWIndexToActual scales hpos offset s hs m j) p
  simpa only [coupledComputedOriginalWRootMatrixName, coupledComputedOriginalWRootMatrix,
    computedOriginalWRootMatrix, coupledComputedOriginalWIndexToActual_eq] using h

/-- Every actual full original-root matrix entry has the same internal integer bound. -/
theorem coupledComputedOriginalWRootMatrix_entry_norm_le (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (roots : computedOriginalWIndex s hs m → Fin s × ℤ) (i j : computedOriginalWIndex s hs m) :
    ‖coupledComputedOriginalWRootMatrix scales hpos offset s hs m roots i j‖ ≤
      (originalComputedWRootRowSize s m : ℝ) :=
  compactOriginalComputedWRootRow_norm_le_size _ hs m _ _

/-- A binary name of a bounded complex value has the safe integer successor bound. -/
theorem complexBinaryName_norm_le_size_succ {a b : ℂ} (B p : ℕ)
    (hab : ‖a - b‖ ≤ 1 / (2 : ℝ) ^ p) (hb : ‖b‖ ≤ (B : ℝ)) : ‖a‖ ≤ ((B + 1 : ℕ) : ℝ) := by
  have he : 1 / (2 : ℝ) ^ p ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ p)
  have h := norm_add_le (a - b) b
  rw [sub_add_cancel] at h
  have hr : ((B + 1 : ℕ) : ℝ) = (B : ℝ) + 1 := by push_cast; rfl
  rw [hr]
  linarith

/-- Every ordinary named entry has a uniform internal bound, for all precision and root tuples. -/
theorem coupledComputedOriginalWRootMatrixName_entry_norm_le (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (roots : computedOriginalWIndex s hs m → Fin s × ℤ) (p : ℕ)
    (i j : computedOriginalWIndex s hs m) :
    ‖rationalComplexValue (coupledComputedOriginalWRootMatrixName scales hpos offset s hs m roots p i j)‖ ≤
      ((originalComputedWRootRowSize s m + 1 : ℕ) : ℝ) :=
  complexBinaryName_norm_le_size_succ _ p
    (coupledComputedOriginalWRootMatrixName_entry_error scales hpos offset s hs m roots p i j)
    (coupledComputedOriginalWRootMatrix_entry_norm_le scales hpos offset s hs m roots i j)

end

end MeyerGeneralProblem.StrongParity
