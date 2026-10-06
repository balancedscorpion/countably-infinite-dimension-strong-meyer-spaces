module

public import MeyerGeneralProblem.Cardinal.Strong.ProductOriginalRows

@[expose] public section

/-! An ACTUAL slab monomial in the complete ORIGINAL two-sided head-row
kernel. The positive and reversed negative convolutions are treated separately;
the genuine zero label is retained in the positive half. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The original corner value `R(1,1)`, as a linear functional on the whole slab. -/
def productCornerFunctional (s : ℕ) : (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ where
  toFun r := ∑ ij, r ij
  map_add' r t := Finset.sum_add_distrib
  map_smul' c r := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

theorem productCornerFunctional_eq_polynomial (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    productCornerFunctional s r = productSlabPolynomial s r 1 1 := by
  simp only [productCornerFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    productSlabPolynomial, one_pow, mul_one]

/-- A genuine diagonal slab index below the deleted top corner. -/
def productInteriorIndex (s h : ℕ) (hh : h < s) : productNumeratorIndex s :=
  ⟨(⟨h, by omega⟩, ⟨h, by omega⟩), by
    intro heq
    have hhs := congrArg (fun p : Fin (s + 1) × Fin (s + 1) => (p.1 : ℕ)) heq
    change h = s at hhs
    omega⟩

/-- The literal original numerator `Z^h W^h`, with coefficient one. -/
def productInteriorMonomial (s h : ℕ) (hh : h < s) : productNumeratorIndex s → ℂ := by
  classical
  exact Pi.single (productInteriorIndex s h hh) 1

theorem productInteriorMonomial_corner (s h : ℕ) (hh : h < s) :
    productCornerFunctional s (productInteriorMonomial s h hh) = 1 := by
  classical
  simp [productCornerFunctional, productInteriorMonomial]

theorem productInteriorMonomial_upper_zero (s h : ℕ) (hh : h < s) (k n : ℕ)
    (hk : k < h ∨ n < h) :
    productSlabUpperCoefficient s (productInteriorMonomial s h hh) k n = 0 := by
  classical
  unfold productSlabUpperCoefficient
  apply Finset.sum_eq_zero
  intro ij _
  by_cases hij : ij = productInteriorIndex s h hh
  · subst ij
    have hnot : ¬(h ≤ k ∧ h ≤ n) := by omega
    change (if h ≤ k ∧ h ≤ n then _ else 0) = 0
    rw [ite_eq_right hnot]
  · have hz : productInteriorMonomial s h hh ij = 0 := by
      simp [productInteriorMonomial, hij]
    simp only [hz, zero_mul, ite_self]

theorem productInteriorMonomial_lower_zero (s h : ℕ) (hh : h < s) (k n : ℕ)
    (hk : k < s - h ∨ n < s - h) :
    productSlabLowerCoefficient s (productInteriorMonomial s h hh) k n = 0 := by
  classical
  unfold productSlabLowerCoefficient
  have hz : productReciprocalSlabCoefficient s (productInteriorMonomial s h hh) k n = 0 := by
    unfold productReciprocalSlabCoefficient
    apply Finset.sum_eq_zero
    intro ij _
    by_cases hij : ij = productInteriorIndex s h hh
    · subst ij
      have hnot : ¬(s - h ≤ k ∧ s - h ≤ n) := by omega
      change (if s - h ≤ k ∧ s - h ≤ n then _ else 0) = 0
      rw [ite_eq_right hnot]
    · have hz : productInteriorMonomial s h hh ij = 0 := by
        simp [productInteriorMonomial, hij]
      simp only [hz, zero_mul, ite_self]
  rw [hz, mul_zero]

/-- The actual middle monomial for every product order at least two. -/
def productMiddleMonomial (s : ℕ) (hs : 2 ≤ s) : productNumeratorIndex s → ℂ :=
  productInteriorMonomial s (s / 2) (by omega)

theorem productMiddleMonomial_corner (s : ℕ) (hs : 2 ≤ s) :
    productCornerFunctional s (productMiddleMonomial s hs) = 1 :=
  productInteriorMonomial_corner _ _ _

theorem productMiddleMonomial_original_head_zero (s : ℕ) (hs : 2 ≤ s)
    (x : spectralConeCarrier.subtype) (hx : |(x : ℝ)| ≤ ((s / 2 : ℕ) : ℝ) / 2) :
    productOriginalSpectralRow s x (productMiddleMonomial s hs) = 0 := by
  obtain ⟨p, rfl⟩ := spectralConeIndexPoint_bijective.2 x
  rw [productOriginalSpectralRow_eq_coefficient, productSpectralCoefficient_at_label]
  have hh : 0 < (s / 2 : ℕ) := by omega
  have hhr : 0 < ((s / 2 : ℕ) : ℝ) := by exact_mod_cast hh
  rcases p with p | p
  · have hk : p.1 < s / 2 := by
      have hb := (positiveConeFrequency_coordinate_le p).1
      simp only [spectralConeIndexPoint, spectralConeIndexFrequency,
        abs_of_nonneg (positiveConeFrequency_nonneg p)] at hx
      exact_mod_cast (show (p.1 : ℝ) < ((s / 2 : ℕ) : ℝ) by linarith)
    simp only [productConeIndexCoefficient, productMiddleMonomial,
      productInteriorMonomial_upper_zero _ _ _ _ _ (Or.inl hk), zero_mul]
  · have hk : p.val.1 < s - s / 2 := by
      have hb := (positiveConeFrequency_coordinate_le p.val).1
      simp only [spectralConeIndexPoint, spectralConeIndexFrequency, abs_neg,
        abs_of_nonneg (positiveConeFrequency_nonneg p.val)] at hx
      have hk' : p.val.1 < s / 2 := by
        exact_mod_cast (show (p.val.1 : ℝ) < ((s / 2 : ℕ) : ℝ) by linarith)
      omega
    simp only [productConeIndexCoefficient, productMiddleMonomial,
      productInteriorMonomial_lower_zero _ _ _ _ _ (Or.inl hk), neg_zero, zero_mul]

theorem productMiddleMonomial_mem_original_head_kernel (s : ℕ) (hs : 2 ≤ s)
    (F : Set ℝ) (hF : ∀ x ∈ F, |x| ≤ ((s / 2 : ℕ) : ℝ) / 2) :
    productMiddleMonomial s hs ∈ productOriginalDeletionKernel s ∅ F := by
  rw [mem_productOriginalDeletionKernel_iff]
  exact ⟨by simp, fun x hx => productMiddleMonomial_original_head_zero s hs x (hF x hx)⟩

end

end MeyerGeneralProblem.StrongParity
