module

public import MeyerGeneralProblem.Cardinal.Strong.RationalQuarterCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadTriangular

@[expose] public section

/-! The actual original head diagonals and their inverses are EXACT rational
quarter phases, independent of any derivative or numerical pivot oracle. -/

namespace MeyerGeneralProblem.StrongParity

/-- The literal original signed pivot, computed exactly on rational coordinates. -/
def rationalOriginalHeadPivot (s : ℕ) (head : productOriginalHeadLabel s) : ℚ × ℚ :=
  match head.val with
  | .inl p => rationalNegativeQuarterCoefficient p.2 1
  | .inr p => rationalQuarterCoefficient p.val.2 (-((-1 : ℚ) ^ s))

/-- Exact rational inversion of each original unit quarter-phase pivot. -/
def rationalOriginalHeadPivotInverse (s : ℕ) (head : productOriginalHeadLabel s) : ℚ × ℚ :=
  rationalComplexConj (rationalOriginalHeadPivot s head)

/-- Every computed original pivot has actual complex norm exactly one. -/
theorem rationalOriginalHeadPivot_norm_one (s : ℕ) (head : productOriginalHeadLabel s) :
    ‖rationalComplexValue (rationalOriginalHeadPivot s head)‖ = 1 := by
  rcases head with ⟨p | p, hp⟩
  · simp [rationalOriginalHeadPivot, rationalNegativeQuarterCoefficient_value, unitPhase_norm]
  · simp [rationalOriginalHeadPivot, rationalQuarterCoefficient_value,
      norm_mul, norm_neg, norm_pow, unitPhase_norm]

/-- The exact rational inversion is the inverse of the actual original pivot. -/
theorem rationalOriginalHeadPivotInverse_value (s : ℕ) (head : productOriginalHeadLabel s) :
    rationalComplexValue (rationalOriginalHeadPivotInverse s head) =
      (rationalComplexValue (rationalOriginalHeadPivot s head))⁻¹ := by
  rw [rationalOriginalHeadPivotInverse, rationalComplexValue_conj]
  symm
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, rationalOriginalHeadPivot_norm_one]
  simp

/-- The exact rational program is the diagonal of EACH actual original signed head row. -/
theorem rationalOriginalHeadPivot_value {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (head : productOriginalHeadLabel s) :
    rationalComplexValue (rationalOriginalHeadPivot s head) =
      CompactOriginal.productOriginalHeadRow block head
        (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs head)) := by
  rcases head with ⟨p | p, hp⟩
  · change rationalComplexValue (rationalNegativeQuarterCoefficient p.2 1) =
      CompactOriginal.productOriginalSpectralRow block (spectralConeIndexPoint (.inl p))
        (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs ⟨.inl p, hp⟩))
    rw [rationalNegativeQuarterCoefficient_value,
      CompactOriginal.productOriginalSpectralRow_coordinate_positive]
    norm_num only [Rat.cast_one]
    change (1 : ℂ) * unitPhase _ =
      (if p.1 ≤ p.1 ∧ p.2 ≤ p.2 then
        compactOriginalUpperCoefficient block (p.1 - p.1) (p.2 - p.2) else 0) * unitPhase _
    simp [compactOriginalUpperCoefficient_zero_zero]
  · have hlt := productOriginalHeadCoordinates_lt s hs ⟨.inr p, hp⟩
    change p.val.1 < s ∧ p.val.2 < s at hlt
    change rationalComplexValue (rationalQuarterCoefficient p.val.2 (-((-1 : ℚ) ^ s))) =
      CompactOriginal.productOriginalSpectralRow block (spectralConeIndexPoint (.inr p))
        (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs ⟨.inr p, hp⟩))
    rw [rationalQuarterCoefficient_value,
      CompactOriginal.productOriginalSpectralRow_coordinate_negative]
    change _ = -((-1 : ℂ) ^ s * (if s - (s - p.val.1) ≤ p.val.1 ∧
      s - (s - p.val.2) ≤ p.val.2 then compactOriginalUpperCoefficient block
      (p.val.1 - (s - (s - p.val.1))) (p.val.2 - (s - (s - p.val.2))) else 0)) * unitPhase _
    rw [Nat.sub_sub_self hlt.1.le, Nat.sub_sub_self hlt.2.le]
    simp [compactOriginalUpperCoefficient_zero_zero]

end MeyerGeneralProblem.StrongParity
