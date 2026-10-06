module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixGeometry
public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalPolynomial

@[expose] public section

/-! The actual COMPLETE mixed-prefix original polynomial at its common scale.
All sheets of every block participate. The nonzero coefficient motif, complete
real root union, and nonvanishing at EVERY common module label are derived from
the internally scheduled coupled data, including the original quarter phase. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Literal positive original polynomial of ALL complete scheduled prefix blocks. -/
def originalScheduledPrefixPolynomial (bound : ℕ → ℕ) (k : ℕ) : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  ∏ i : Fin k, ∏ j : Fin (originalReflectedOrderSchedule bound i.val),
    originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
      ((originalScheduledParameterBlock bound i.val).parameter j)

/-- The empty complete prefix has the actual constant polynomial one. -/
@[simp] theorem originalScheduledPrefixPolynomial_zero (bound : ℕ → ℕ) :
    originalScheduledPrefixPolynomial bound 0 = 1 := by simp [originalScheduledPrefixPolynomial]

/-- Every sheet factor evaluates at precisely its ORIGINAL private geometric scale. -/
theorem originalScheduledPrefixPolynomial_entireEvaluation (bound : ℕ → ℕ) (k : ℕ) (z : ℂ) :
    originalPositivePolynomialEvaluation (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z
      (originalScheduledPrefixPolynomial bound k) =
        ∏ i : Fin k, compactOriginalComplexSheetProduct (originalScheduledParameterBlock bound i.val)
          (((1 / originalPrivateScale (originalReflectedPrimeSchedule bound i.val) : ℝ) : ℂ) * z) := by
  simp only [originalScheduledPrefixPolynomial, map_prod, originalPositivePolynomialEvaluation_sheet,
    originalScheduledPrefixCoordinateDilation_ratio, compactOriginalComplexSheetProduct]

/-- The literal real original product of every complete block at its private scale. -/
def originalScheduledPrefixRealSymbol (bound : ℕ → ℕ) (k : ℕ) (x : ℝ) : ℂ :=
  ∏ i : Fin k, compactOriginalRealSheetProduct (originalScheduledParameterBlock bound i.val)
    (x / originalPrivateScale (originalReflectedPrimeSchedule bound i.val))

/-- The complete native positive motif is extracted internally from the actual product. -/
abbrev OriginalScheduledPrefixMotif (bound : ℕ → ℕ) (k : ℕ) :=
  OriginalPositivePolynomialMotif (originalScheduledPrefixPolynomial bound k)

/-- Actual nonnegative coordinates, with ALL equal-frequency collisions already summed. -/
def originalScheduledPrefixPolynomialCoordinates (bound : ℕ → ℕ) (k : ℕ) :
    OriginalScheduledPrefixMotif bound k → ℕ × ℕ :=
  originalPositivePolynomialCoordinates (originalScheduledPrefixPolynomial bound k)

/-- Actual finite original coefficients of the complete mixed product. -/
def originalScheduledPrefixPolynomialCoefficient (bound : ℕ → ℕ) (k : ℕ) :
    OriginalScheduledPrefixMotif bound k → ℂ :=
  originalPositivePolynomialCoefficient (originalScheduledPrefixPolynomial bound k)

/-- Exact finite positive-frequency representation of the literal full original real product. -/
theorem originalScheduledPrefixPolynomial_finiteSymbol (bound : ℕ → ℕ) (k : ℕ) (x : ℝ) :
    finitePositiveExponentialSymbol (originalPositivePolynomialFrequency
      (originalPrivateScale (originalScheduledPrefixDenominator bound k))
      (originalScheduledPrefixPolynomialCoordinates bound k))
      (originalScheduledPrefixPolynomialCoefficient bound k) x = originalScheduledPrefixRealSymbol bound k x := by
  unfold originalScheduledPrefixPolynomialCoordinates originalScheduledPrefixPolynomialCoefficient
  rw [originalPositivePolynomialEvaluation_finiteSymbol,
    originalScheduledPrefixPolynomial_entireEvaluation]
  unfold originalScheduledPrefixRealSymbol
  apply Finset.prod_congr rfl
  intro i _
  rw [show (((1 / originalPrivateScale (originalReflectedPrimeSchedule bound i.val) : ℝ) : ℂ) * (x : ℂ)) =
    ((x / originalPrivateScale (originalReflectedPrimeSchedule bound i.val) : ℝ) : ℂ) by push_cast; ring]
  exact compactOriginalComplexSheetProduct_ofReal _ _

/-- Exact full physical root characterisation of EVERY original block factor. -/
theorem originalScheduledBlockRealSymbol_zero_iff (bound : ℕ → ℕ) (i : ℕ) (x : ℝ) :
    compactOriginalRealSheetProduct (originalScheduledParameterBlock bound i)
      (x / originalPrivateScale (originalReflectedPrimeSchedule bound i)) = 0 ↔
        x ∈ (originalScheduledFullPhysicalCarrier bound i).carrier := by
  have hs := (originalPrivateScale_pos _ (originalScheduledBlockPrime_pos bound i)).ne'
  constructor
  · intro h
    refine ⟨x / originalPrivateScale (originalReflectedPrimeSchedule bound i), h, ?_⟩
    exact mul_div_cancel₀ x hs
  · rintro ⟨y, hy, rfl⟩
    change compactOriginalRealSheetProduct (originalScheduledParameterBlock bound i) y = 0 at hy
    change compactOriginalRealSheetProduct (originalScheduledParameterBlock bound i)
      (originalPrivateScale (originalReflectedPrimeSchedule bound i) * y /
        originalPrivateScale (originalReflectedPrimeSchedule bound i)) = 0
    rw [mul_div_cancel_left₀ y hs]
    exact hy

/-- ALL actual roots of the full finite product are precisely the complete physical root union. -/
theorem originalScheduledPrefixRealSymbol_zero_iff (bound : ℕ → ℕ) (k : ℕ) (x : ℝ) :
    originalScheduledPrefixRealSymbol bound k x = 0 ↔ x ∈ originalScheduledPrefixRootSet bound k := by
  simp only [originalScheduledPrefixRealSymbol, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    originalScheduledPrefixRootSet, Set.mem_iUnion, originalScheduledBlockRealSymbol_zero_iff]

/-- Actual root vanishing for EVERY complete physical point, including all deleted roots. -/
theorem originalScheduledPrefixPolynomial_vanishes (bound : ℕ → ℕ) (k : ℕ)
    (x : ℝ) (hx : x ∈ originalScheduledPrefixRootSet bound k) :
    finitePositiveExponentialSymbol (originalPositivePolynomialFrequency
      (originalPrivateScale (originalScheduledPrefixDenominator bound k))
      (originalScheduledPrefixPolynomialCoordinates bound k))
      (originalScheduledPrefixPolynomialCoefficient bound k) x = 0 := by
  rw [originalScheduledPrefixPolynomial_finiteSymbol]
  exact (originalScheduledPrefixRealSymbol_zero_iff bound k x).mpr hx

/-- EVERY complete scheduled physical root avoids the full rational module. -/
theorem originalScheduledPrefixRootSet_not_mem_module (bound : ℕ → ℕ) (k : ℕ) (x : ℝ)
    (hx : x ∈ originalScheduledPrefixRootSet bound k) : x ∉ parityRationalCoarseModule := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j, n, rfl⟩ := (originalScheduledFullPhysicalCarrier_iff_label bound i.val x).mp hi
  exact originalScheduledPhysicalRoot_not_mem bound (⟨i.val, j⟩, n)

/-- EVERY integer label at ANY positive natural common scale lies in the rational module. -/
theorem originalScaledModuleFrequency_mem_rational_module (m : ℕ) (hm : 0 < m) (z : ℤ × ℤ) :
    originalScaledModuleFrequency (originalPrivateScale m) z ∈ parityRationalCoarseModule := by
  refine ⟨(z.1 : ℚ) / (m : ℚ), (z.2 : ℚ) / (m : ℚ), ?_⟩
  have hc := parityDilationUnit_pos.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [originalScaledModuleFrequency, originalPrivateScale]
  push_cast
  field_simp

/-- ALL native module labels avoid the genuine original finite-prefix symbol, internally. -/
theorem originalScheduledPrefixPolynomial_nonzero_on_module (bound : ℕ → ℕ) (k : ℕ) (z : ℤ × ℤ) :
    finitePositiveExponentialSymbol (originalPositivePolynomialFrequency
      (originalPrivateScale (originalScheduledPrefixDenominator bound k))
      (originalScheduledPrefixPolynomialCoordinates bound k))
      (originalScheduledPrefixPolynomialCoefficient bound k)
      (originalScaledModuleFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z) ≠ 0 := by
  rw [originalScheduledPrefixPolynomial_finiteSymbol]
  intro h
  exact originalScheduledPrefixRootSet_not_mem_module bound k _
    ((originalScheduledPrefixRealSymbol_zero_iff bound k _).mp h)
    (originalScaledModuleFrequency_mem_rational_module _ (originalScheduledPrefixDenominator_pos bound k) z)

/-- The actual complete original prefix polynomial is nonzero, without a supplied certificate. -/
theorem originalScheduledPrefixPolynomial_ne_zero (bound : ℕ → ℕ) (k : ℕ) :
    originalScheduledPrefixPolynomial bound k ≠ 0 := by
  intro h
  have he := originalScheduledPrefixPolynomial_nonzero_on_module bound k (0, 0)
  unfold originalScheduledPrefixPolynomialCoordinates originalScheduledPrefixPolynomialCoefficient at he
  rw [originalPositivePolynomialEvaluation_finiteSymbol, h, map_zero] at he
  exact he rfl

/-- The ACTUAL coefficient motif of every finite prefix is nonempty, including the empty prefix. -/
theorem originalScheduledPrefixMotif_nonempty (bound : ℕ → ℕ) (k : ℕ) :
    Nonempty (OriginalScheduledPrefixMotif bound k) := by
  have hc : (originalScheduledPrefixPolynomial bound k).coeff ≠ 0 := by
    intro h
    apply originalScheduledPrefixPolynomial_ne_zero bound k
    exact AddMonoidAlgebra.coeff_injective (h.trans (by simp))
  obtain ⟨p, hp⟩ := Finsupp.support_nonempty_iff.mpr hc
  exact ⟨⟨p, hp⟩⟩

end
end MeyerGeneralProblem.StrongParity
