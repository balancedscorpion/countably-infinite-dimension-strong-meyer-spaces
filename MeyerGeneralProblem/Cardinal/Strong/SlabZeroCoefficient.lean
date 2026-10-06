module

public import MeyerGeneralProblem.Cardinal.Strong.SlabPowerSeries

@[expose] public section

/-! The original zero-frequency coefficient, obtained from the actual quotient series. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem productSheetPolynomial_zero_zero (s : ℕ) : productSheetPolynomial s 0 0 = 1 := by
  simp only [productSheetPolynomial, sheetPolynomial, mul_zero, sub_zero, add_zero,
    Finset.prod_const_one]

/-- The upper zero coefficient is exactly the original numerator's constant value. -/
theorem productSlabUpperCoefficient_zero_zero (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    productSlabUpperCoefficient s r 0 0 = productSlabPolynomial s r 0 0 := by
  have hs := productSlabUpperCoefficient_hasSum s r
    (Z := 0) (W := 0) (by norm_num) (by norm_num)
  have hsingle : HasSum (fun p : ℕ × ℕ =>
      productSlabUpperCoefficient s r p.1 p.2 * (0 : ℂ) ^ p.1 * (0 : ℂ) ^ p.2)
      (productSlabUpperCoefficient s r 0 0) := by
    convert! hasSum_single (f := fun p : ℕ × ℕ =>
      productSlabUpperCoefficient s r p.1 p.2 * (0 : ℂ) ^ p.1 * (0 : ℂ) ^ p.2)
      (0, 0) (fun p hp => ?_) using 1
    · simp only [pow_zero, mul_one]
    · by_cases hk : p.1 = 0
      · have hn : p.2 ≠ 0 := fun hn => hp (Prod.ext hk hn)
        simp only [zero_pow hn, mul_zero]
      · simp only [zero_pow hk, mul_zero, zero_mul]
  simpa only [productSheetPolynomial_zero_zero, div_one] using (hsingle.unique hs)

end

end MeyerGeneralProblem.StrongParity
