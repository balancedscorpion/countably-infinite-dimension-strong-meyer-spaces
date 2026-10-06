module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalSpectralRows
public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalCoefficientSize

@[expose] public section

/-! Computed uniform sizes for ALL original signed coordinates and the complete
retained head matrix, both at actual coefficients and at every name precision. -/

namespace MeyerGeneralProblem.StrongParity

/-- Exact integer coordinate size, retaining both full original slab masks. -/
def originalSpectralCoordinateSize (s : ℕ) (ij : productNumeratorIndex s) (label : spectralConeIndex) : ℕ :=
  match label with
  | .inl p => if (ij.val.1 : ℕ) ≤ p.1 ∧ (ij.val.2 : ℕ) ≤ p.2 then
      finiteOriginalUpperCoefficientSize s (p.1 - ij.val.1) (p.2 - ij.val.2) else 0
  | .inr p => if s - (ij.val.1 : ℕ) ≤ p.val.1 ∧ s - (ij.val.2 : ℕ) ≤ p.val.2 then
      finiteOriginalUpperCoefficientSize s (p.val.1 - (s - ij.val.1))
        (p.val.2 - (s - ij.val.2)) else 0

/-- Uniform integer size of the entire retained ORIGINAL head matrix. -/
def originalHeadMatrixSize (s : ℕ) (A : Finset (productOriginalHeadLabel s)) : ℕ :=
  1 + ∑ head ∈ A, ∑ ij : productNumeratorIndex s, originalSpectralCoordinateSize s ij head.val

/-- Every actual original signed row coordinate satisfies the computed size. -/
theorem originalSpectralCoordinate_norm_le_size {s : ℕ} (block : CompactOriginalParameterBlock s)
    (ij : productNumeratorIndex s) (label : spectralConeIndex) :
    ‖CompactOriginal.productOriginalSpectralRow block (spectralConeIndexPoint label)
      (productSlabCoordinateVector s ij)‖ ≤ (originalSpectralCoordinateSize s ij label : ℝ) := by
  cases label with
  | inl p =>
    rw [CompactOriginal.productOriginalSpectralRow_coordinate_positive]
    unfold originalSpectralCoordinateSize
    split_ifs with h
    · simpa only [h, ite_true, ite_false, true_and, and_true, norm_mul, unitPhase_norm, mul_one] using
        compactOriginalUpperCoefficient_norm_le_size block (p.1 - ij.val.1) (p.2 - ij.val.2)
    · simp only [h, ite_false, zero_mul, neg_zero, mul_zero, norm_zero, Rat.cast_zero]
      positivity
  | inr p =>
    rw [CompactOriginal.productOriginalSpectralRow_coordinate_negative]
    unfold originalSpectralCoordinateSize
    split_ifs with h
    · simpa only [h, ite_true, ite_false, true_and, and_true, norm_mul, norm_neg, norm_pow, norm_one, one_pow, one_mul,
        unitPhase_norm, mul_one] using compactOriginalUpperCoefficient_norm_le_size block
          (p.val.1 - (s - ij.val.1)) (p.val.2 - (s - ij.val.2))
    · simp only [h, ite_false, zero_mul, neg_zero, mul_zero, norm_zero, Rat.cast_zero]
      positivity

/-- Every ordinary original signed row-name coordinate satisfies the same computed size. -/
theorem coupledCompactOriginalSpectralCoordinateName_norm_le_size (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (ij : productNumeratorIndex s)
    (label : spectralConeIndex) (precision : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalSpectralCoordinateName scales hpos offset s ij label precision)‖ ≤
      (originalSpectralCoordinateSize s ij label : ℝ) := by
  cases label with
  | inl p =>
    unfold coupledCompactOriginalSpectralCoordinateName rationalNamedOriginalSpectralCoordinate originalSpectralCoordinateSize
    rw [rationalNegativeQuarterCoefficient_value]
    split_ifs with h
    · simpa only [h, ite_true, ite_false, true_and, and_true, norm_mul, unitPhase_norm, mul_one, coupledCompactOriginalUpperCoefficientName] using
        coupledCompactOriginalUpperCoefficientName_norm_le_size scales hpos offset s
          (p.1 - ij.val.1) (p.2 - ij.val.2) precision
    · simp only [h, ite_false, zero_mul, neg_zero, mul_zero, norm_zero, Rat.cast_zero]
      positivity
  | inr p =>
    unfold coupledCompactOriginalSpectralCoordinateName rationalNamedOriginalSpectralCoordinate originalSpectralCoordinateSize
    rw [rationalQuarterCoefficient_value]
    split_ifs with h
    · push_cast
      simpa only [h, ite_true, ite_false, true_and, and_true, norm_mul, norm_neg, norm_pow, norm_one, one_pow, one_mul,
        unitPhase_norm, mul_one, coupledCompactOriginalUpperCoefficientName] using coupledCompactOriginalUpperCoefficientName_norm_le_size scales hpos offset s
          (p.val.1 - (s - ij.val.1)) (p.val.2 - (s - ij.val.2)) precision
    · simp only [h, ite_false, zero_mul, neg_zero, mul_zero, norm_zero, Rat.cast_zero]
      positivity

/-- The computed whole matrix size bounds every original retained coordinate size. -/
theorem originalSpectralCoordinateSize_le_headMatrix (s : ℕ)
    (A : Finset (productOriginalHeadLabel s)) (head : A) (ij : productNumeratorIndex s) :
    originalSpectralCoordinateSize s ij head.val.val ≤ originalHeadMatrixSize s A := by
  have h1 : originalSpectralCoordinateSize s ij head.val.val ≤
      ∑ kl : productNumeratorIndex s, originalSpectralCoordinateSize s kl head.val.val :=
    Finset.single_le_sum (f := fun kl : productNumeratorIndex s => originalSpectralCoordinateSize s kl head.val.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ij)
  have h2 : (∑ kl : productNumeratorIndex s, originalSpectralCoordinateSize s kl head.val.val) ≤
      ∑ p ∈ A, ∑ kl : productNumeratorIndex s, originalSpectralCoordinateSize s kl p.val :=
    Finset.single_le_sum (f := fun p : productOriginalHeadLabel s => ∑ kl : productNumeratorIndex s, originalSpectralCoordinateSize s kl p.val) (fun _ _ => Nat.zero_le _) head.property
  unfold originalHeadMatrixSize
  omega

end MeyerGeneralProblem.StrongParity
