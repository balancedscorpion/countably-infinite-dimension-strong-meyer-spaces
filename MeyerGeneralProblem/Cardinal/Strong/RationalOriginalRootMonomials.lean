module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalRootPhases
public import MeyerGeneralProblem.Cardinal.Strong.FiniteComplexPowers
public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalHeadProjection

@[expose] public section

/-! Ordinary names for EVERY literal original slab monomial at EVERY labelled
native root. The complete two-variable power error is budgeted internally. -/

namespace MeyerGeneralProblem.StrongParity

/-- Safe whole-slab torus monomial size for the original square degree box. -/
def originalRootMonomialSize (s : ℕ) : ℕ := 2 ^ (2 * s)

/-- Whole-slab two-variable power sensitivity, computed from the actual order. -/
def originalRootMonomialSensitivity (s : ℕ) : ℕ := finiteComplexPowerSensitivity (2 * s)

/-- Complete rational original monomial evaluation at specified phase precision. -/
def coupledCompactOriginalRootMonomialAt (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (i : Fin s) (n : ℤ) (j : productNumeratorIndex s) (p : ℕ) : ℚ × ℚ :=
  rationalComplexMul
    (rationalComplexPow (coupledCompactOriginalRootUName scales hpos offset s i n p) j.val.1.val)
    (rationalComplexPow (coupledCompactOriginalRootVName scales hpos offset s i n p) j.val.2.val)

/-- Ordinary binary monomial name with the whole two-variable precision budget. -/
def coupledCompactOriginalRootMonomialName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (i : Fin s) (n : ℤ) (j : productNumeratorIndex s) (p : ℕ) : ℚ × ℚ :=
  coupledCompactOriginalRootMonomialAt scales hpos offset s i n j
    (p + originalRootMonomialSensitivity s)

noncomputable section

/-- Every original slab exponent pair obeys the complete square-box degree budget. -/
theorem productNumeratorIndex_degree_le_twice (s : ℕ) (j : productNumeratorIndex s) :
    j.val.1.val + j.val.2.val ≤ 2 * s := by
  have h1 := j.val.1.isLt
  have h2 := j.val.2.isLt
  omega

/-- All phase errors propagate through BOTH original monomial powers. -/
theorem coupledCompactOriginalRootMonomialAt_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (i : Fin s) (n : ℤ)
    (j : productNumeratorIndex s) (p : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalRootMonomialAt scales hpos offset s i n j p) -
      unitPhase (compactOriginalRootLabel n
        ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter i)) ^ j.val.1.val *
      unitPhase (beta * compactOriginalRootLabel n
        ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter i) - 1 / 4) ^ j.val.2.val‖ ≤
          (originalRootMonomialSensitivity s : ℝ) * (1 / (2 : ℝ) ^ p) := by
  rw [coupledCompactOriginalRootMonomialAt, rationalComplexMul_value,
    rationalComplexPow_value, rationalComplexPow_value]
  have h := complexBivariateMonomial_sub_norm_le
    (coupledCompactOriginalRootUName_norm_le_two scales hpos offset s i n p)
    (by rw [unitPhase_norm]; norm_num)
    (coupledCompactOriginalRootVName_norm_le_two scales hpos offset s i n p)
    (by rw [unitPhase_norm]; norm_num) (1 / (2 : ℝ) ^ p) (by positivity)
    (coupledCompactOriginalRootUName_error scales hpos offset s i n p)
    (coupledCompactOriginalRootVName_error scales hpos offset s i n p) j.val.1.val j.val.2.val
  exact h.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast finiteComplexPowerSensitivity_mono (productNumeratorIndex_degree_le_twice s j))
    (by positivity))

/-- EVERY actual original monomial at EVERY labelled root has the requested binary error. -/
theorem coupledCompactOriginalRootMonomialName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (i : Fin s) (n : ℤ)
    (j : productNumeratorIndex s) (p : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalRootMonomialName scales hpos offset s i n j p) -
      unitPhase (compactOriginalRootLabel n
        ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter i)) ^ j.val.1.val *
      unitPhase (beta * compactOriginalRootLabel n
        ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter i) - 1 / 4) ^ j.val.2.val‖ ≤
          1 / (2 : ℝ) ^ p :=
  (coupledCompactOriginalRootMonomialAt_error scales hpos offset s i n j
    (p + originalRootMonomialSensitivity s)).trans
      (integer_sensitivity_binary_shift (originalRootMonomialSensitivity s) p)

/-- Every finite phase program output monomial has the internally computed size. -/
theorem coupledCompactOriginalRootMonomialAt_norm_le_size (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (i : Fin s) (n : ℤ)
    (j : productNumeratorIndex s) (p : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalRootMonomialAt scales hpos offset s i n j p)‖ ≤
      (originalRootMonomialSize s : ℝ) := by
  rw [coupledCompactOriginalRootMonomialAt, rationalComplexMul_value,
    rationalComplexPow_value, rationalComplexPow_value, norm_mul]
  calc
    _ ≤ (2 : ℝ) ^ j.val.1.val * (2 : ℝ) ^ j.val.2.val := by
      exact mul_le_mul
        (complexPow_norm_le_two_pow (coupledCompactOriginalRootUName_norm_le_two scales hpos offset s i n p) _)
        (complexPow_norm_le_two_pow (coupledCompactOriginalRootVName_norm_le_two scales hpos offset s i n p) _)
        (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ (j.val.1.val + j.val.2.val) := (pow_add _ _ _).symm
    _ ≤ (2 : ℝ) ^ (2 * s) := by
      have hd := productNumeratorIndex_degree_le_twice s j
      gcongr <;> norm_num
    _ = _ := by simp [originalRootMonomialSize]

/-- Every normalized original monomial name retains the same uniform size bound. -/
theorem coupledCompactOriginalRootMonomialName_norm_le_size (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (i : Fin s) (n : ℤ)
    (j : productNumeratorIndex s) (p : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalRootMonomialName scales hpos offset s i n j p)‖ ≤
      (originalRootMonomialSize s : ℝ) :=
  coupledCompactOriginalRootMonomialAt_norm_le_size scales hpos offset s i n j _

end

end MeyerGeneralProblem.StrongParity
