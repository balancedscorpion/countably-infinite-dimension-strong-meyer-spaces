module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalHeadBasisNames
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadCornerBasis

@[expose] public section

/-! Exact rational corner correction and its complete finite coordinate error
budget. The correcting vector is the literal original middle monomial. -/

namespace MeyerGeneralProblem.StrongParity

/-- Ordinary rational subtraction of the complete corner multiple. -/
def rationalOriginalCornerCorrection (s : ℕ) (hs : 2 ≤ s)
    (v : productNumeratorIndex s → ℚ × ℚ) (k : productNumeratorIndex s) : ℚ × ℚ :=
  rationalComplexSub (v k)
    (rationalComplexMul (rationalComplexSum Finset.univ v)
      (rationalOriginalMonomial s (productInteriorIndex s (s / 2) (by omega)) k))

/-- The computed correction is exactly the original full corner subtraction. -/
theorem rationalOriginalCornerCorrection_value (s : ℕ) (hs : 2 ≤ s)
    (v : productNumeratorIndex s → ℚ × ℚ) (k : productNumeratorIndex s) :
    rationalComplexValue (rationalOriginalCornerCorrection s hs v k) =
      rationalComplexValue (v k) - (∑ j : productNumeratorIndex s, rationalComplexValue (v j)) *
        productMiddleMonomial s hs k := by
  simp only [rationalOriginalCornerCorrection, rationalComplexSub_value,
    rationalComplexMul_value, rationalComplexSum_value, rationalOriginalMonomial_value,
    productMiddleMonomial, productInteriorMonomial, productSlabCoordinateVector]

/-- The actual middle monomial has coordinate norm at most one. -/
theorem productMiddleMonomial_coordinate_norm_le_one (s : ℕ) (hs : 2 ≤ s)
    (k : productNumeratorIndex s) : ‖productMiddleMonomial s hs k‖ ≤ 1 := by
  unfold productMiddleMonomial productInteriorMonomial
  by_cases hk : k = productInteriorIndex s (s / 2) (by omega)
  · simp [Pi.single_apply, hk]
  · simp [Pi.single_apply, hk]

/-- All coordinates of a complete finite corner correction retain an explicit error budget. -/
theorem originalCornerCorrection_sub_norm_le (s : ℕ) (hs : 2 ≤ s)
    (v w : productNumeratorIndex s → ℂ) (L : ℕ) (epsilon : ℝ)
    (hv : ∀ k, ‖v k - w k‖ ≤ (L : ℝ) * epsilon) (k : productNumeratorIndex s) :
    ‖(v k - (∑ j : productNumeratorIndex s, v j) * productMiddleMonomial s hs k) -
      (w k - (∑ j : productNumeratorIndex s, w j) * productMiddleMonomial s hs k)‖ ≤
        (((Fintype.card (productNumeratorIndex s) + 1) * L : ℕ) : ℝ) * epsilon := by
  have hsum : ‖(∑ j : productNumeratorIndex s, v j) - (∑ j : productNumeratorIndex s, w j)‖ ≤
      (Fintype.card (productNumeratorIndex s) : ℝ) * ((L : ℝ) * epsilon) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : productNumeratorIndex s, ‖v j - w j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : productNumeratorIndex s, (L : ℝ) * epsilon := Finset.sum_le_sum (fun j _ => hv j)
      _ = _ := by simp
  have hmul : ‖((∑ j : productNumeratorIndex s, v j) - (∑ j : productNumeratorIndex s, w j)) *
      productMiddleMonomial s hs k‖ ≤ (Fintype.card (productNumeratorIndex s) : ℝ) * ((L : ℝ) * epsilon) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (productMiddleMonomial_coordinate_norm_le_one s hs k)
      (norm_nonneg _)).trans (by simpa only [mul_one] using hsum)
  calc
    _ = ‖(v k - w k) - ((∑ j : productNumeratorIndex s, v j) -
          (∑ j : productNumeratorIndex s, w j)) * productMiddleMonomial s hs k‖ := by congr 1; ring
    _ ≤ ‖v k - w k‖ + ‖((∑ j : productNumeratorIndex s, v j) -
          (∑ j : productNumeratorIndex s, w j)) * productMiddleMonomial s hs k‖ := norm_sub_le _ _
    _ ≤ (L : ℝ) * epsilon + (Fintype.card (productNumeratorIndex s) : ℝ) * ((L : ℝ) * epsilon) :=
      add_le_add (hv k) hmul
    _ = _ := by push_cast; ring

end MeyerGeneralProblem.StrongParity
