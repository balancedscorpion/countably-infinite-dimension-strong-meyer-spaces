module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalCoefficientNames
public import MeyerGeneralProblem.Cardinal.Strong.RationalQuarterCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalSlabPivots
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadLabels

@[expose] public section

/-! Ordinary rational programs for ALL original signed spectral row coordinates.
The full upper and reversed lower slab conditions, signs and exact quarter phases
are retained; the zero coefficient appears only on the original positive side. -/

namespace MeyerGeneralProblem.StrongParity

/-- The original signed spectral coordinate, computed from ordinary parameter names. -/
def rationalNamedOriginalSpectralCoordinate {s : ℕ} (names : Fin s → ℕ → ℚ)
    (ij : productNumeratorIndex s) (label : spectralConeIndex) (precision : ℕ) : ℚ × ℚ :=
  match label with
  | .inl p => rationalNegativeQuarterCoefficient p.2
      (if (ij.val.1 : ℕ) ≤ p.1 ∧ (ij.val.2 : ℕ) ≤ p.2 then
        rationalNamedOriginalUpperCoefficient names (p.1 - ij.val.1) (p.2 - ij.val.2) precision else 0)
  | .inr p => rationalQuarterCoefficient p.val.2
      (-((-1 : ℚ) ^ s * (if s - (ij.val.1 : ℕ) ≤ p.val.1 ∧ s - (ij.val.2 : ℕ) ≤ p.val.2 then
        rationalNamedOriginalUpperCoefficient names (p.val.1 - (s - ij.val.1))
          (p.val.2 - (s - ij.val.2)) precision else 0)))

/-- The ordinary signed spectral row program on an internally constructed compact block. -/
def coupledCompactOriginalSpectralCoordinateName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (ij : productNumeratorIndex s) (label : spectralConeIndex) (precision : ℕ) : ℚ × ℚ :=
  rationalNamedOriginalSpectralCoordinate
    (fun i : Fin s => (coupledOriginalParameterNames scales hpos
      disjointOriginalParameterSlot (offset + i.val)).val) ij label precision

/-- EVERY actual original signed row coordinate has its implemented ordinary binary name. -/
theorem coupledCompactOriginalSpectralCoordinateName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (ij : productNumeratorIndex s)
    (label : spectralConeIndex) (precision : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalSpectralCoordinateName scales hpos offset s ij label precision) -
      CompactOriginal.productOriginalSpectralRow (coupledCompactOriginalParameterBlock scales hpos offset s)
        (spectralConeIndexPoint label) (productSlabCoordinateVector s ij)‖ ≤
      1 / (2 : ℝ) ^ precision := by
  cases label with
  | inl p =>
    unfold coupledCompactOriginalSpectralCoordinateName rationalNamedOriginalSpectralCoordinate
    rw [rationalNegativeQuarterCoefficient_value, CompactOriginal.productOriginalSpectralRow_coordinate_positive]
    split_ifs with h
    · rw [← sub_mul, norm_mul, unitPhase_norm, mul_one]
      exact coupledCompactOriginalUpperCoefficientName_error scales hpos offset s
        (p.1 - ij.val.1) (p.2 - ij.val.2) precision
    · simp
  | inr p =>
    unfold coupledCompactOriginalSpectralCoordinateName rationalNamedOriginalSpectralCoordinate
    rw [rationalQuarterCoefficient_value, CompactOriginal.productOriginalSpectralRow_coordinate_negative]
    split_ifs with h
    · push_cast
      rw [← sub_mul, norm_mul, unitPhase_norm, mul_one, neg_sub_neg, ← mul_sub,
        norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_sub_rev]
      exact coupledCompactOriginalUpperCoefficientName_error scales hpos offset s
        (p.val.1 - (s - ij.val.1)) (p.val.2 - (s - ij.val.2)) precision
    · simp

/-- All retained actual ORIGINAL head row entries inherit the same rational error proof. -/
theorem coupledCompactOriginalHeadCoordinateName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (ij : productNumeratorIndex s)
    (head : productOriginalHeadLabel s) (precision : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalSpectralCoordinateName scales hpos offset s ij head.val precision) -
      CompactOriginal.productOriginalHeadRow (coupledCompactOriginalParameterBlock scales hpos offset s)
        head (productSlabCoordinateVector s ij)‖ ≤ 1 / (2 : ℝ) ^ precision :=
  coupledCompactOriginalSpectralCoordinateName_error scales hpos offset s ij head.val precision

end MeyerGeneralProblem.StrongParity
