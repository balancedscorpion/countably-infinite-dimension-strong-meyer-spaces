module

public import MeyerGeneralProblem.Cardinal.Strong.SlabPowerSeries

@[expose] public section

/-! Literal reciprocity of the original product and complete numerator slab.
The reversed numerator excludes its constant term because the original
slab excludes only its top corner. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem sheetPolynomial_reciprocal (a : ℂ) {Z W : ℂ} (hZ : Z ≠ 0) (hW : W ≠ 0) :
    Z * W * sheetPolynomial a Z⁻¹ W⁻¹ = -sheetPolynomial a Z W := by
  unfold sheetPolynomial
  field_simp
  ring

theorem productSheetPolynomial_reciprocal (s : ℕ) {Z W : ℂ}
    (hZ : Z ≠ 0) (hW : W ≠ 0) :
    (Z * W) ^ s * productSheetPolynomial s Z⁻¹ W⁻¹ =
      (-1 : ℂ) ^ s * productSheetPolynomial s Z W := by
  calc
    _ = ∏ i : Fin s, (Z * W) * sheetPolynomial (productSheetParameter s i) Z⁻¹ W⁻¹ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, productSheetPolynomial, mul_pow]
    _ = ∏ i : Fin s, -sheetPolynomial (productSheetParameter s i) Z W := by
      apply Finset.prod_congr rfl
      intro i _
      exact sheetPolynomial_reciprocal (productSheetParameter s i : ℂ) hZ hW
    _ = ∏ i : Fin s, (-1 : ℂ) * sheetPolynomial (productSheetParameter s i) Z W := by
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, productSheetPolynomial]

/-- The reciprocal numerator uses every original slab index. -/
def productReciprocalSlabPolynomial (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (Z W : ℂ) : ℂ :=
  ∑ ij, r ij * Z ^ (s - (ij.val.1 : ℕ)) * W ^ (s - (ij.val.2 : ℕ))

theorem mul_inv_power_eq_sub {Z : ℂ} (hZ : Z ≠ 0) {i s : ℕ} (hi : i ≤ s) :
    Z ^ s * (Z⁻¹) ^ i = Z ^ (s - i) := by
  calc
    _ = (Z ^ (s - i) * Z ^ i) * (Z⁻¹) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    _ = _ := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hZ, one_pow, mul_one]

theorem productSlabPolynomial_reciprocal (s : ℕ) (r : productNumeratorIndex s → ℂ)
    {Z W : ℂ} (hZ : Z ≠ 0) (hW : W ≠ 0) :
    (Z * W) ^ s * productSlabPolynomial s r Z⁻¹ W⁻¹ =
      productReciprocalSlabPolynomial s r Z W := by
  unfold productSlabPolynomial productReciprocalSlabPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  have hi : (ij.val.1 : ℕ) ≤ s := by omega
  have hj : (ij.val.2 : ℕ) ≤ s := by omega
  calc
    _ = r ij * (Z ^ s * (Z⁻¹) ^ (ij.val.1 : ℕ)) *
        (W ^ s * (W⁻¹) ^ (ij.val.2 : ℕ)) := by rw [mul_pow]; ring
    _ = _ := by rw [mul_inv_power_eq_sub hZ hi, mul_inv_power_eq_sub hW hj]

/-- Excluding the original top corner gives the actual reversed constant term zero. -/
theorem productReciprocalSlabPolynomial_zero_zero (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    productReciprocalSlabPolynomial s r 0 0 = 0 := by
  unfold productReciprocalSlabPolynomial
  apply Finset.sum_eq_zero
  intro ij _
  have hij : s - (ij.val.1 : ℕ) ≠ 0 ∨ s - (ij.val.2 : ℕ) ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    have hi : (ij.val.1 : ℕ) = s := by omega
    have hj : (ij.val.2 : ℕ) = s := by omega
    exact ij.property (by apply Prod.ext <;> apply Fin.ext <;> assumption)
  rcases hij with hi | hj
  · simp [zero_pow hi]
  · simp [zero_pow hj]

end

end MeyerGeneralProblem.StrongParity
