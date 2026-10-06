module

public import MeyerGeneralProblem.Cardinal.Strong.ReciprocalSlabSeries

@[expose] public section

/-! The literal lower series evaluates to the same original exterior quotient. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem productSlabQuotient_reciprocal (s : ℕ) (r : productNumeratorIndex s → ℂ)
    {Z W : ℂ} (hZ : Z ≠ 0) (hW : W ≠ 0) :
    (-1 : ℂ) ^ s * (productReciprocalSlabPolynomial s r Z⁻¹ W⁻¹ /
      productSheetPolynomial s Z⁻¹ W⁻¹) =
        productSlabPolynomial s r Z W / productSheetPolynomial s Z W := by
  let ε : ℂ := (-1) ^ s
  let A : ℂ := (Z⁻¹ * W⁻¹) ^ s
  have he : ε * ε = 1 := by
    dsimp [ε]
    rw [← mul_pow]
    norm_num
  have he0 : ε ≠ 0 := pow_ne_zero _ (by norm_num)
  have hA0 : A ≠ 0 := pow_ne_zero _ (mul_ne_zero (inv_ne_zero hZ) (inv_ne_zero hW))
  have hP : A * productSheetPolynomial s Z W = ε * productSheetPolynomial s Z⁻¹ W⁻¹ := by
    simpa only [A, ε, inv_inv] using
      productSheetPolynomial_reciprocal s (inv_ne_zero hZ) (inv_ne_zero hW)
  have hR : productReciprocalSlabPolynomial s r Z⁻¹ W⁻¹ =
      A * productSlabPolynomial s r Z W := by
    simpa only [A, inv_inv] using
      (productSlabPolynomial_reciprocal s r (inv_ne_zero hZ) (inv_ne_zero hW)).symm
  have hp : productSheetPolynomial s Z⁻¹ W⁻¹ = ε * A * productSheetPolynomial s Z W := by
    calc
      _ = ε * (ε * productSheetPolynomial s Z⁻¹ W⁻¹) := by rw [← mul_assoc, he, one_mul]
      _ = ε * (A * productSheetPolynomial s Z W) := by rw [hP]
      _ = _ := by ring
  change ε * (_ / _) = _
  rw [← mul_div_assoc, hR, hp, ← mul_assoc]
  exact mul_div_mul_left _ _ (mul_ne_zero he0 hA0)

/-- The complete original lower expansion, with its sign and zero term retained. -/
theorem productSlabLowerCoefficient_exterior_hasSum (s : ℕ)
    (r : productNumeratorIndex s → ℂ) {Z W : ℂ}
    (hZ : Z ≠ 0) (hW : W ≠ 0) (hZi : ‖Z⁻¹‖ < 1) (hWi : ‖W⁻¹‖ < 1) :
    HasSum (fun p : ℕ × ℕ => productSlabLowerCoefficient s r p.1 p.2 *
      (Z⁻¹) ^ p.1 * (W⁻¹) ^ p.2)
      (productSlabPolynomial s r Z W / productSheetPolynomial s Z W) := by
  rw [← productSlabQuotient_reciprocal s r hZ hW]
  exact productSlabLowerCoefficient_hasSum s r hZi hWi

end

end MeyerGeneralProblem.StrongParity
