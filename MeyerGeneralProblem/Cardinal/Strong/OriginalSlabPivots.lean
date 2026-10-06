module

public import MeyerGeneralProblem.Cardinal.Strong.ProductOriginalRows

@[expose] public section

/-! Exact entries of the ORIGINAL upper and reversed lower rows on literal
slab coordinate vectors. The reciprocal constant coefficient and both actual
quarter phases are proved, rather than supplied by a rank certificate. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem productUpperCoefficient_zero_zero (s : ℕ) : productUpperCoefficient s 0 0 = 1 := by
  have hs := productUpperCoefficient_bidisk_hasSum s
    (Z := 0) (W := 0) (by norm_num) (by norm_num)
  have hsingle : HasSum (fun p : ℕ × ℕ =>
      productUpperCoefficient s p.1 p.2 * (0 : ℂ) ^ p.1 * (0 : ℂ) ^ p.2)
      (productUpperCoefficient s 0 0) := by
    convert! hasSum_single (f := fun p : ℕ × ℕ =>
      productUpperCoefficient s p.1 p.2 * (0 : ℂ) ^ p.1 * (0 : ℂ) ^ p.2)
      (0, 0) (fun p hp => ?_) using 1
    · simp only [pow_zero, mul_one]
    · by_cases hk : p.1 = 0
      · have hn : p.2 ≠ 0 := fun hn => hp (Prod.ext hk hn)
        simp only [zero_pow hn, mul_zero]
      · simp only [zero_pow hk, mul_zero, zero_mul]
  simpa only [productSheetPolynomial_zero_zero, inv_one] using hsingle.unique hs

/-- A literal original slab coordinate vector, with its single coefficient one. -/
def productSlabCoordinateVector (s : ℕ) (ij : productNumeratorIndex s) :
    productNumeratorIndex s → ℂ := by
  classical
  exact Pi.single ij 1

theorem productSlabUpperCoefficient_coordinate (s : ℕ) (ij : productNumeratorIndex s)
    (k n : ℕ) :
    productSlabUpperCoefficient s (productSlabCoordinateVector s ij) k n =
      if (ij.val.1 : ℕ) ≤ k ∧ (ij.val.2 : ℕ) ≤ n then
        productUpperCoefficient s (k - ij.val.1) (n - ij.val.2) else 0 := by
  classical
  unfold productSlabUpperCoefficient
  rw [Finset.sum_eq_single ij]
  · simp only [productSlabCoordinateVector, Pi.single_eq_same, one_mul]
  · intro kl _ hkl
    have hz : productSlabCoordinateVector s ij kl = 0 := by
      simp [productSlabCoordinateVector, hkl]
    simp only [hz, zero_mul, ite_self]
  · intro h
    exact False.elim (h (Finset.mem_univ ij))

theorem productReciprocalSlabCoefficient_coordinate (s : ℕ) (ij : productNumeratorIndex s)
    (k n : ℕ) :
    productReciprocalSlabCoefficient s (productSlabCoordinateVector s ij) k n =
      if s - (ij.val.1 : ℕ) ≤ k ∧ s - (ij.val.2 : ℕ) ≤ n then
        productUpperCoefficient s (k - (s - ij.val.1)) (n - (s - ij.val.2)) else 0 := by
  classical
  unfold productReciprocalSlabCoefficient
  rw [Finset.sum_eq_single ij]
  · simp only [productSlabCoordinateVector, Pi.single_eq_same, one_mul]
  · intro kl _ hkl
    have hz : productSlabCoordinateVector s ij kl = 0 := by
      simp [productSlabCoordinateVector, hkl]
    simp only [hz, zero_mul, ite_self]
  · intro h
    exact False.elim (h (Finset.mem_univ ij))

theorem productOriginalSpectralRow_coordinate_positive (s : ℕ) (ij : productNumeratorIndex s)
    (p : ℕ × ℕ) :
    productOriginalSpectralRow s (spectralConeIndexPoint (.inl p))
      (productSlabCoordinateVector s ij) =
      (if (ij.val.1 : ℕ) ≤ p.1 ∧ (ij.val.2 : ℕ) ≤ p.2 then
        productUpperCoefficient s (p.1 - ij.val.1) (p.2 - ij.val.2) else 0) *
          unitPhase (-(p.2 : ℝ) / 4) := by
  calc
    _ = productSpectralCoefficient s (productSlabCoordinateVector s ij)
        (spectralConeIndexPoint (.inl p)) := productOriginalSpectralRow_eq_coefficient _ _ _
    _ = productConeIndexCoefficient s (productSlabCoordinateVector s ij) (.inl p) :=
      productSpectralCoefficient_at_label _ _ _
    _ = _ := congrArg (fun c : ℂ => c * unitPhase (-(p.2 : ℝ) / 4))
      (productSlabUpperCoefficient_coordinate s ij p.1 p.2)

theorem productOriginalSpectralRow_coordinate_negative (s : ℕ) (ij : productNumeratorIndex s)
    (p : {p : ℕ × ℕ // p ≠ (0, 0)}) :
    productOriginalSpectralRow s (spectralConeIndexPoint (.inr p))
      (productSlabCoordinateVector s ij) =
      -((-1 : ℂ) ^ s * (if s - (ij.val.1 : ℕ) ≤ p.val.1 ∧
          s - (ij.val.2 : ℕ) ≤ p.val.2 then
        productUpperCoefficient s (p.val.1 - (s - ij.val.1))
          (p.val.2 - (s - ij.val.2)) else 0)) * unitPhase ((p.val.2 : ℝ) / 4) := by
  calc
    _ = productSpectralCoefficient s (productSlabCoordinateVector s ij)
        (spectralConeIndexPoint (.inr p)) := productOriginalSpectralRow_eq_coefficient _ _ _
    _ = productConeIndexCoefficient s (productSlabCoordinateVector s ij) (.inr p) :=
      productSpectralCoefficient_at_label _ _ _
    _ = _ := congrArg (fun c : ℂ => -((-1 : ℂ) ^ s * c) * unitPhase ((p.val.2 : ℝ) / 4))
      (productReciprocalSlabCoefficient_coordinate s ij p.val.1 p.val.2)

end

end MeyerGeneralProblem.StrongParity
