module

public import MeyerGeneralProblem.Cardinal.Strong.FiniteTaylorBounds

@[expose] public section

/-! Computed integer size and perturbation budgets for EVERY original reciprocal
coefficient.  All two-index degree compositions are retained. -/

namespace MeyerGeneralProblem.StrongParity

/-- Integer size budget for an original reciprocal coefficient. -/
def finiteOriginalUpperCoefficientSize (s k n : ℕ) : ℕ :=
  ∑ v ∈ productZCompositions s k,
    finiteTaylorProductSize (fun i j => sheetFiniteWCoefficientSize (v i) j) n

/-- Integer sensitivity to uniform parameter error for an original coefficient. -/
def finiteOriginalUpperCoefficientSensitivity (s k n : ℕ) : ℕ :=
  ∑ v ∈ productZCompositions s k,
    finiteTaylorProductSensitivity (fun i j => sheetFiniteWCoefficientSize (v i) j)
      (fun i j => sheetFiniteWCoefficientSensitivity (v i) j) n

/-- Every actual finite reciprocal computation satisfies its computed size bound. -/
theorem finiteOriginalUpperCoefficient_abs_le_size {s : ℕ} (a : Fin s → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (k n : ℕ) :
    |finiteOriginalUpperCoefficient a k n| ≤ (finiteOriginalUpperCoefficientSize s k n : ℝ) := by
  rw [finiteOriginalUpperCoefficient, finiteOriginalUpperCoefficientSize]
  push_cast
  calc
    _ ≤ ∑ v ∈ productZCompositions s k,
        |finiteTaylorProduct (fun i j => sheetFiniteWCoefficient (a i) (v i) j) n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v hv
      exact finiteTaylorProduct_abs_le_size _ _
        (fun i j => sheetFiniteWCoefficient_abs_le_size (ha i) (v i) j) n

/-- Every actual finite reciprocal computation satisfies its computed error bound. -/
theorem finiteOriginalUpperCoefficient_abs_sub_le_sensitivity {s : ℕ} (a b : Fin s → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) (epsilon : ℝ)
    (hab : ∀ i, |a i - b i| ≤ epsilon) (k n : ℕ) :
    |finiteOriginalUpperCoefficient a k n - finiteOriginalUpperCoefficient b k n| ≤
      (finiteOriginalUpperCoefficientSensitivity s k n : ℝ) * epsilon := by
  rw [finiteOriginalUpperCoefficient, finiteOriginalUpperCoefficient,
    finiteOriginalUpperCoefficientSensitivity, ← Finset.sum_sub_distrib]
  push_cast
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ v ∈ productZCompositions s k,
        |finiteTaylorProduct (fun i j => sheetFiniteWCoefficient (a i) (v i) j) n -
          finiteTaylorProduct (fun i j => sheetFiniteWCoefficient (b i) (v i) j) n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v hv
      exact finiteTaylorProduct_abs_sub_le_sensitivity _ _ _ _ epsilon
        (fun i j => sheetFiniteWCoefficient_abs_le_size (ha i) (v i) j)
        (fun i j => sheetFiniteWCoefficient_abs_le_size (hb i) (v i) j)
        (fun i j => sheetFiniteWCoefficient_abs_sub_le_sensitivity
          (ha i) (hb i) (hab i) (v i) j) n

/-- A computed integer sensitivity shift pays the requested binary output precision. -/
theorem integer_sensitivity_binary_shift (L p : ℕ) :
    (L : ℝ) * (1 / (2 : ℝ) ^ (p + L)) ≤ 1 / (2 : ℝ) ^ p := by
  have hL : (L : ℝ) ≤ (2 : ℝ) ^ L := by
    induction L with
    | zero => norm_num
    | succ L ih =>
      have hone : (1 : ℝ) ≤ (2 : ℝ) ^ L := one_le_pow₀ (by norm_num)
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      nlinarith
  have hpow : (2 : ℝ) ^ L ≠ 0 := by positivity
  calc
    _ ≤ (2 : ℝ) ^ L * (1 / (2 : ℝ) ^ (p + L)) := by gcongr
    _ = _ := by rw [pow_add]; field_simp

end MeyerGeneralProblem.StrongParity
