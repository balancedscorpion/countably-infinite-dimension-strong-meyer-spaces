module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalRowBounds
public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalHeadPivots
public import MeyerGeneralProblem.Cardinal.Strong.FiniteEliminationBounds
public import MeyerGeneralProblem.Cardinal.Strong.CoordinateOriginalElimination
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadFreeBasis

@[expose] public section

/-! Ordinary finite rational names for the complete actual original head
projection. Exact quarter-phase diagonal inverses are computed internally. -/

namespace MeyerGeneralProblem.StrongParity

/-- Head equality uses only the signed natural coordinates, ignoring proofs. -/
instance originalHeadLabel_decidableEq (s : ℕ) : DecidableEq (productOriginalHeadLabel s) := by
  unfold productOriginalHeadLabel spectralConeIndex
  infer_instance

/-- Coordinate equality is decided on the two bounded natural coordinates. -/
instance originalNumeratorIndex_decidableEq (s : ℕ) : DecidableEq (productNumeratorIndex s) := by
  unfold productNumeratorIndex
  infer_instance

/-- Computed sensitivity of the WHOLE original head projection. -/
def originalHeadProjectionSensitivity (s : ℕ) (A : Finset (productOriginalHeadLabel s)) : ℕ :=
  coordinateEliminationSensitivity (originalHeadMatrixSize s A) A.card
    (Fintype.card (productNumeratorIndex s)) (s + 1)

/-- Ordinary exact rational original monomial. -/
def rationalOriginalMonomial (s : ℕ) (j : productNumeratorIndex s) :
    productNumeratorIndex s → ℚ × ℚ := fun k => if k = j then (1, 0) else (0, 0)

/-- Whole rational degree elimination at a specified entry precision. -/
def coupledCompactOriginalHeadProjectionAt (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (A : Finset (productOriginalHeadLabel s))
    (j : productNumeratorIndex s) (precision : ℕ) : productNumeratorIndex s → ℚ × ℚ :=
  rationalComplexDegreeElimination
    (fun head : A => fun k => coupledCompactOriginalSpectralCoordinateName scales hpos offset s k head.val.val precision)
    (fun head : A => rationalOriginalHeadPivotInverse s head.val)
    (fun head : A => productOriginalHeadPivotIndex s hs head.val)
    (fun head : A => productOriginalHeadDegree s head.val)
    (s + 1) (rationalOriginalMonomial s j)

/-- Ordinary binary name of EVERY coordinate of the original projected monomial. -/
def coupledCompactOriginalHeadProjectionName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (A : Finset (productOriginalHeadLabel s))
    (j : productNumeratorIndex s) (precision : ℕ) : productNumeratorIndex s → ℚ × ℚ :=
  coupledCompactOriginalHeadProjectionAt scales hpos offset s hs A j
    (precision + originalHeadProjectionSensitivity s A)

/-- The ordinary rational monomial has exactly the original monomial value. -/
theorem rationalOriginalMonomial_value (s : ℕ) (j k : productNumeratorIndex s) :
    rationalComplexValue (rationalOriginalMonomial s j k) = productSlabCoordinateVector s j k := by
  by_cases h : k = j <;> simp [rationalOriginalMonomial, rationalComplexValue, productSlabCoordinateVector, Pi.single_apply, h]

/-- All exact original inverse pivots have norm one, hence need no division oracle. -/
theorem rationalOriginalHeadPivotInverse_norm_one (s : ℕ) (head : productOriginalHeadLabel s) :
    ‖rationalComplexValue (rationalOriginalHeadPivotInverse s head)‖ = 1 := by
  rw [rationalOriginalHeadPivotInverse_value, norm_inv, rationalOriginalHeadPivot_norm_one, inv_one]

/-- The analytic monomial equals the same single vector with constructive coordinate equality. -/
theorem productSlabCoordinateVector_eq_constructive_single (s : ℕ) (j : productNumeratorIndex s) :
    productSlabCoordinateVector s j = Pi.single j (1 : ℂ) := by
  funext k
  by_cases h : k = j <;> simp [productSlabCoordinateVector, Pi.single_apply, h]

/-- The complete actual coordinate algorithm is the specified ORIGINAL head projection. -/
theorem complexCoordinateDegreeElimination_eq_compact_headProjection {s : ℕ}
    (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) (v : productNumeratorIndex s → ℂ)
    (k : productNumeratorIndex s) :
    complexCoordinateDegreeElimination
      (fun head : A => fun j => CompactOriginal.productOriginalHeadRow block head.val
        (productSlabCoordinateVector s j))
      (fun head : A => rationalComplexValue (rationalOriginalHeadPivotInverse s head.val))
      (fun head : A => productOriginalHeadPivotIndex s hs head.val)
      (fun head : A => productOriginalHeadDegree s head.val) (s + 1) v k =
        CompactOriginal.productOriginalHeadProjection block hs A v k := by
  have hinv : (fun head : A => rationalComplexValue (rationalOriginalHeadPivotInverse s head.val)) =
      (fun head : A => (CompactOriginal.productOriginalRetainedHeadRow block A head
        (Pi.single (productOriginalHeadPivotIndex s hs head.val) 1))⁻¹) := by
    funext head
    have hp := rationalOriginalHeadPivot_value block hs head.val
    rw [productSlabCoordinateVector_eq_constructive_single] at hp
    simpa only [CompactOriginal.productOriginalRetainedHeadRow] using
      (rationalOriginalHeadPivotInverse_value s head.val).trans
        (congrArg (fun z : ℂ => z⁻¹) hp)
  rw [hinv]
  have h := complexCoordinateDegreeElimination_eq_original
    (CompactOriginal.productOriginalRetainedHeadRow block A)
    (fun head : A => productOriginalHeadPivotIndex s hs head.val)
    (fun head : A => productOriginalHeadDegree s head.val) (s + 1) v k
  simp only [CompactOriginal.productOriginalRetainedHeadRow,
    CompactOriginal.productOriginalHeadProjection, productOriginalHeadPivotVector,
    productOriginalHeadRetainedDegree, productSlabCoordinateVector_eq_constructive_single] at h ⊢
  convert! h using 1
  have hpivot : productOriginalHeadPivotVector s hs A =
      (fun head : A => Pi.single (productOriginalHeadPivotIndex s hs head.val) (1 : ℂ)) := by
    funext head
    exact productSlabCoordinateVector_eq_constructive_single s (productOriginalHeadPivotIndex s hs head.val)
  rw [hpivot]
  rfl

/-- Every entry of the actual whole head matrix is bounded by the computed integer. -/
theorem compactOriginalHeadCoordinate_norm_le_matrix {s : ℕ}
    (block : CompactOriginalParameterBlock s) (A : Finset (productOriginalHeadLabel s))
    (head : A) (k : productNumeratorIndex s) :
    ‖CompactOriginal.productOriginalHeadRow block head.val (productSlabCoordinateVector s k)‖ ≤
      (originalHeadMatrixSize s A : ℝ) :=
  (originalSpectralCoordinate_norm_le_size block k head.val.val).trans
    (by exact_mod_cast originalSpectralCoordinateSize_le_headMatrix s A head k)

/-- Every named entry of the whole head matrix obeys that same integer bound. -/
theorem coupledCompactOriginalHeadCoordinateName_norm_le_matrix (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (A : Finset (productOriginalHeadLabel s))
    (head : A) (k : productNumeratorIndex s) (precision : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalSpectralCoordinateName scales hpos offset s k head.val.val precision)‖ ≤
      (originalHeadMatrixSize s A : ℝ) :=
  (coupledCompactOriginalSpectralCoordinateName_norm_le_size scales hpos offset s k head.val.val precision).trans
    (by exact_mod_cast originalSpectralCoordinateSize_le_headMatrix s A head k)

end MeyerGeneralProblem.StrongParity
