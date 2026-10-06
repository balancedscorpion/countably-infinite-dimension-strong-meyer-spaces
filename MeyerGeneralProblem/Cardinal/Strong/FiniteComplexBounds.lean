module

public import MeyerGeneralProblem.Cardinal.Strong.FiniteComplexElimination

@[expose] public section

/-! Complete finite complex dot-product size and perturbation estimates. -/

namespace MeyerGeneralProblem.StrongParity

/-- Complete finite complex dot products satisfy an explicit integer size bound. -/
theorem finiteComplexDot_norm_le {J : Type*} [Fintype J] (a v : J → ℂ) (M B : ℕ)
    (ha : ∀ j, ‖a j‖ ≤ (M : ℝ)) (hv : ∀ j, ‖v j‖ ≤ (B : ℝ)) :
    ‖∑ j : J, a j * v j‖ ≤ (Fintype.card J * M * B : ℕ) := by
  calc
    _ ≤ ∑ j : J, ‖a j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : J, (M : ℝ) * (B : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (ha j) (hv j) (norm_nonneg _) (Nat.cast_nonneg M)
    _ = _ := by simp; push_cast; ring

/-- Product perturbation at literal complex coordinates. -/
theorem complexProduct_sub_norm_le {a b x y : ℂ} (M B L : ℕ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (ha : ‖a‖ ≤ (M : ℝ)) (hy : ‖y‖ ≤ (B : ℝ))
    (hab : ‖a - b‖ ≤ epsilon) (hxy : ‖x - y‖ ≤ (L : ℝ) * epsilon) :
    ‖a * x - b * y‖ ≤ ((B + M * L : ℕ) : ℝ) * epsilon := by
  calc
    _ = ‖a * (x - y) + (a - b) * y‖ := by congr 1; ring
    _ ≤ ‖a * (x - y)‖ + ‖(a - b) * y‖ := norm_add_le _ _
    _ = ‖a‖ * ‖x - y‖ + ‖a - b‖ * ‖y‖ := by rw [norm_mul, norm_mul]
    _ ≤ (M : ℝ) * ((L : ℝ) * epsilon) + epsilon * (B : ℝ) :=
      add_le_add (mul_le_mul ha hxy (norm_nonneg _) (Nat.cast_nonneg M))
        (mul_le_mul hab hy (norm_nonneg _) he)
    _ = _ := by push_cast; ring

/-- Complete finite complex dot products retain all entry and vector errors. -/
theorem finiteComplexDot_sub_norm_le {J : Type*} [Fintype J]
    (a b v w : J → ℂ) (M B L : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (ha : ∀ j, ‖a j‖ ≤ (M : ℝ)) (hw : ∀ j, ‖w j‖ ≤ (B : ℝ))
    (hab : ∀ j, ‖a j - b j‖ ≤ epsilon)
    (hvw : ∀ j, ‖v j - w j‖ ≤ (L : ℝ) * epsilon) :
    ‖(∑ j : J, a j * v j) - (∑ j : J, b j * w j)‖ ≤
      ((Fintype.card J * (B + M * L) : ℕ) : ℝ) * epsilon := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : J, ‖a j * v j - b j * w j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : J, ((B + M * L : ℕ) : ℝ) * epsilon :=
      Finset.sum_le_sum (fun j _ => complexProduct_sub_norm_le M B L epsilon he
        (ha j) (hw j) (hab j) (hvw j))
    _ = _ := by simp; push_cast; ring

/-- Any filtered finite sum retains the complete ambient cardinal bound. -/
theorem finiteFilteredComplexSum_norm_le {I : Type*} [Fintype I]
    (A : Finset I) (f : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ i ∈ A, ‖f i‖ ≤ C) : ‖∑ i ∈ A, f i‖ ≤ (Fintype.card I : ℝ) * C := by
  calc
    _ ≤ ∑ i ∈ A, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ A, C := Finset.sum_le_sum hf
    _ = (A.card : ℝ) * C := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast Finset.card_le_univ A

end MeyerGeneralProblem.StrongParity
