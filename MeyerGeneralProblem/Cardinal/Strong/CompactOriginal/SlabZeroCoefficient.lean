module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SlabCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.SlabZeroCoefficient
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SlabPowerSeries

@[expose] public section

/-! Original SlabZeroCoefficient for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The upper zero coefficient is exactly the original numerator's constant value. -/
theorem productSlabUpperCoefficient_zero_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    productSlabUpperCoefficient block r 0 0 = productSlabPolynomial s r 0 0 := by
  have hs := productSlabUpperCoefficient_hasSum block r
    (Z := 0) (W := 0) (by norm_num) (by norm_num)
  have hsingle : HasSum (fun p : ℕ × ℕ =>
      productSlabUpperCoefficient block r p.1 p.2 * (0 : ℂ) ^ p.1 * (0 : ℂ) ^ p.2)
      (productSlabUpperCoefficient block r 0 0) := by
    convert! hasSum_single (f := fun p : ℕ × ℕ =>
      productSlabUpperCoefficient block r p.1 p.2 * (0 : ℂ) ^ p.1 * (0 : ℂ) ^ p.2)
      (0, 0) (fun p hp => ?_) using 1
    · simp only [pow_zero, mul_one]
    · by_cases hk : p.1 = 0
      · have hn : p.2 ≠ 0 := fun hn => hp (Prod.ext hk hn)
        simp only [zero_pow hn, mul_zero]
      · simp only [zero_pow hk, mul_zero, zero_mul]
  simpa only [compactOriginalSheetPolynomial_zero_zero block, div_one] using (hsingle.unique hs)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
