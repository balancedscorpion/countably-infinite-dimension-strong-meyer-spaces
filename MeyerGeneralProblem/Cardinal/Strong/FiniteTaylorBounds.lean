module

public import MeyerGeneralProblem.Cardinal.Strong.FiniteCoefficientBounds

@[expose] public section

/-! Explicit size and sensitivity of the COMPLETE finite Taylor convolution.
All natural budgets are finite programs. Their bounds hold for every coefficient
and every entire finite family, with no supplied coefficient oracle. -/

namespace MeyerGeneralProblem.StrongParity

/-- Integer size budget of the whole finite convolution. -/
def finiteTaylorProductSize : {s : ℕ} → (Fin s → ℕ → ℕ) → ℕ → ℕ
  | 0, _, n => if n = 0 then 1 else 0
  | s + 1, B, n => ∑ j ∈ Finset.range (n + 1),
      B 0 j * finiteTaylorProductSize (fun i : Fin s => B i.succ) (n - j)

/-- Integer perturbation budget of the whole finite convolution. -/
def finiteTaylorProductSensitivity :
    {s : ℕ} → (Fin s → ℕ → ℕ) → (Fin s → ℕ → ℕ) → ℕ → ℕ
  | 0, _, _, _ => 0
  | s + 1, B, L, n => ∑ j ∈ Finset.range (n + 1),
      (L 0 j * finiteTaylorProductSize (fun i : Fin s => B i.succ) (n - j) +
      B 0 j * finiteTaylorProductSensitivity (fun i : Fin s => B i.succ)
        (fun i => L i.succ) (n - j))

/-- Product perturbation with explicit size and error bounds. -/
theorem real_bounded_product_perturbation {a b x y B1 B2 L1 L2 epsilon : ℝ}
    (ha : |a| ≤ B1) (hy : |y| ≤ B2)
    (hab : |a - b| ≤ L1 * epsilon) (hxy : |x - y| ≤ L2 * epsilon) :
    |a * x - b * y| ≤ (L1 * B2 + B1 * L2) * epsilon := by
  calc
    _ = |a * (x - y) + (a - b) * y| := by congr 1; ring
    _ ≤ |a * (x - y)| + |(a - b) * y| := abs_add_le _ _
    _ = |a| * |x - y| + |a - b| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ B1 * (L2 * epsilon) + (L1 * epsilon) * B2 :=
      add_le_add (mul_le_mul ha hxy (abs_nonneg _) ((abs_nonneg _).trans ha))
        (mul_le_mul hab hy (abs_nonneg _) ((abs_nonneg _).trans hab))
    _ = _ := by ring

/-- The actual complete convolution satisfies its computed size bound. -/
theorem finiteTaylorProduct_abs_le_size {s : ℕ} (f : Fin s → ℕ → ℝ)
    (B : Fin s → ℕ → ℕ) (hf : ∀ i j, |f i j| ≤ (B i j : ℝ)) (n : ℕ) :
    |finiteTaylorProduct f n| ≤ (finiteTaylorProductSize B n : ℝ) := by
  induction s generalizing n with
  | zero => by_cases hn : n = 0 <;> simp [finiteTaylorProduct, finiteTaylorProductSize, hn]
  | succ s ih =>
    rw [finiteTaylorProduct, finiteTaylorProductSize]
    push_cast
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1),
          |f 0 j * finiteTaylorProduct (fun i : Fin s => f i.succ) (n - j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul (hf 0 j)
          (ih (fun i => f i.succ) (fun i => B i.succ) (fun i j => hf i.succ j) (n - j))
          (abs_nonneg _) (Nat.cast_nonneg _)

/-- The actual complete convolution satisfies its computed perturbation bound. -/
theorem finiteTaylorProduct_abs_sub_le_sensitivity {s : ℕ} (f g : Fin s → ℕ → ℝ)
    (B L : Fin s → ℕ → ℕ) (epsilon : ℝ)
    (hf : ∀ i j, |f i j| ≤ (B i j : ℝ))
    (hg : ∀ i j, |g i j| ≤ (B i j : ℝ))
    (hfg : ∀ i j, |f i j - g i j| ≤ (L i j : ℝ) * epsilon) (n : ℕ) :
    |finiteTaylorProduct f n - finiteTaylorProduct g n| ≤
      (finiteTaylorProductSensitivity B L n : ℝ) * epsilon := by
  induction s generalizing n with
  | zero => simp [finiteTaylorProduct, finiteTaylorProductSensitivity]
  | succ s ih =>
    rw [finiteTaylorProduct, finiteTaylorProduct, finiteTaylorProductSensitivity,
      ← Finset.sum_sub_distrib]
    push_cast
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1),
          |f 0 j * finiteTaylorProduct (fun i : Fin s => f i.succ) (n - j) -
            g 0 j * finiteTaylorProduct (fun i : Fin s => g i.succ) (n - j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        exact real_bounded_product_perturbation (hf 0 j)
          (finiteTaylorProduct_abs_le_size (fun i => g i.succ) (fun i => B i.succ)
            (fun i j => hg i.succ j) (n - j)) (hfg 0 j)
          (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => B i.succ)
            (fun i => L i.succ) (fun i j => hf i.succ j) (fun i j => hg i.succ j)
            (fun i j => hfg i.succ j) (n - j))

end MeyerGeneralProblem.StrongParity
