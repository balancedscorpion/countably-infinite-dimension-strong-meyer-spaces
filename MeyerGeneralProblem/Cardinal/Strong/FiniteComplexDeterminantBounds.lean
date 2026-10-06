module

public import MeyerGeneralProblem.Cardinal.Strong.RationalComplexDeterminant
public import MeyerGeneralProblem.Cardinal.Strong.FiniteComplexBounds

@[expose] public section

/-! Explicit integer perturbation bounds for complete finite complex products
and the entire Leibniz determinant. No numerical rank test is assumed. -/

namespace MeyerGeneralProblem.StrongParity

/-- Integer perturbation budget for a complete product of bounded factors. -/
def finiteComplexProductSensitivity (M n : ℕ) : ℕ := n * M ^ n

/-- Whole determinant perturbation budget, including EVERY permutation and matrix factor. -/
def finiteComplexDetSensitivity (M n : ℕ) : ℕ := n.factorial * finiteComplexProductSensitivity M n

noncomputable section

/-- The complete finite product satisfies the explicit integer norm bound. -/
theorem finiteComplexProduct_norm_le {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (f : ι → ℂ) (M : ℕ) (hf : ∀ i ∈ A, ‖f i‖ ≤ (M : ℝ)) :
    ‖∏ i ∈ A, f i‖ ≤ ((M ^ A.card : ℕ) : ℝ) := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    rw [Finset.prod_insert ha, norm_mul, Finset.card_insert_of_notMem ha, pow_succ, Nat.cast_mul]
    have hi := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    exact (mul_le_mul (hf a (Finset.mem_insert_self _ _)) hi
      (norm_nonneg _) (Nat.cast_nonneg M)).trans_eq (mul_comm _ _)

/-- Complete finite product differences retain every factor error. -/
theorem finiteComplexProduct_sub_norm_le {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (f g : ι → ℂ) (M : ℕ) (hM : 1 ≤ M)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hf : ∀ i ∈ A, ‖f i‖ ≤ (M : ℝ)) (hg : ∀ i ∈ A, ‖g i‖ ≤ (M : ℝ))
    (hfg : ∀ i ∈ A, ‖f i - g i‖ ≤ epsilon) :
    ‖(∏ i ∈ A, f i) - (∏ i ∈ A, g i)‖ ≤
      (finiteComplexProductSensitivity M A.card : ℝ) * epsilon := by
  induction A using Finset.induction_on with
  | empty => simp [finiteComplexProductSensitivity]
  | @insert a A ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h := complexProduct_sub_norm_le M (M ^ A.card)
      (finiteComplexProductSensitivity M A.card) epsilon he
      (hf a (Finset.mem_insert_self _ _))
      (finiteComplexProduct_norm_le A g M (fun i hi => hg i (Finset.mem_insert_of_mem hi)))
      (hfg a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
    have hL : M ^ A.card + M * finiteComplexProductSensitivity M A.card ≤
        finiteComplexProductSensitivity M (A.card + 1) := by
      calc
        _ = (1 + M * A.card) * M ^ A.card := by simp only [finiteComplexProductSensitivity]; ring
        _ ≤ (M + M * A.card) * M ^ A.card := Nat.mul_le_mul_right _ (Nat.add_le_add_right hM _)
        _ = _ := by simp only [finiteComplexProductSensitivity, pow_succ]; ring
    exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hL) he)

/-- The ENTIRE matrix determinant has its explicit whole-permutation error budget. -/
theorem finiteComplexDet_sub_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (M : ℕ) (hM : 1 ≤ M) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hA : ∀ i j, ‖A i j‖ ≤ (M : ℝ)) (hB : ∀ i j, ‖B i j‖ ≤ (M : ℝ))
    (hAB : ∀ i j, ‖A i j - B i j‖ ≤ epsilon) :
    ‖Matrix.det A - Matrix.det B‖ ≤
      (finiteComplexDetSensitivity M (Fintype.card ι) : ℝ) * epsilon := by
  rw [Matrix.det_apply A, Matrix.det_apply B, ← Finset.sum_sub_distrib]
  have ht (p : Equiv.Perm ι) :
      ‖Equiv.Perm.sign p • (∏ i : ι, A (p i) i) - Equiv.Perm.sign p • (∏ i : ι, B (p i) i)‖ ≤
        (finiteComplexProductSensitivity M (Fintype.card ι) : ℝ) * epsilon := by
    have hs : ‖((Equiv.Perm.sign p : ℤ) : ℂ)‖ = 1 := by
      rw [← rationalPermutationSign_value]
      exact rationalPermutationSign_norm_one p
    simp only [Units.smul_def, zsmul_eq_mul, ← mul_sub, norm_mul, hs, one_mul]
    simpa only [Finset.card_univ] using finiteComplexProduct_sub_norm_le Finset.univ
      (fun i => A (p i) i) (fun i => B (p i) i) M hM epsilon he
      (fun i hi => hA (p i) i) (fun i hi => hB (p i) i) (fun i hi => hAB (p i) i)
  calc
    _ ≤ ∑ p : Equiv.Perm ι,
      ‖Equiv.Perm.sign p • (∏ i : ι, A (p i) i) - Equiv.Perm.sign p • (∏ i : ι, B (p i) i)‖ := norm_sum_le _ _
    _ ≤ ∑ _p : Equiv.Perm ι,
      (finiteComplexProductSensitivity M (Fintype.card ι) : ℝ) * epsilon :=
        Finset.sum_le_sum (fun p hp => ht p)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_perm,
        finiteComplexDetSensitivity, Nat.cast_mul]
      ring

end

end MeyerGeneralProblem.StrongParity
