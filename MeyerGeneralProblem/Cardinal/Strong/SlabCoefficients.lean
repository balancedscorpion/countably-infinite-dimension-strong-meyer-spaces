module

public import MeyerGeneralProblem.Cardinal.Strong.BidiskSeries
public import MeyerGeneralProblem.Cardinal.Strong.ProductResidues

@[expose] public section

/-! Literal finite slab multiplication and its actual upper coefficients.
Every original numerator index and every admissible shift is retained. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The original complete slab numerator at two independent complex variables. -/
def productSlabPolynomial (s : ℕ) (r : productNumeratorIndex s → ℂ) (Z W : ℂ) : ℂ :=
  ∑ ij, r ij * Z ^ (ij.val.1 : ℕ) * W ^ (ij.val.2 : ℕ)

theorem productSlabPolynomial_onFlow (s : ℕ) (r : productNumeratorIndex s → ℂ) (x : ℝ) :
    productSlabPolynomial s r (unitPhase x) (unitPhase (beta * x - 1 / 4)) =
      productSlabNumerator s r x := rfl

/-- The literal upper coefficient after complete finite slab convolution. -/
def productSlabUpperCoefficient (s : ℕ) (r : productNumeratorIndex s → ℂ) (k n : ℕ) : ℂ :=
  ∑ ij, if (ij.val.1 : ℕ) ≤ k ∧ (ij.val.2 : ℕ) ≤ n then
    r ij * productUpperCoefficient s (k - ij.val.1) (n - ij.val.2) else 0

theorem productSlabUpperCoefficient_norm_le (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (k n : ℕ) :
    ‖productSlabUpperCoefficient s r k n‖ ≤
      productSlabCoefficientBound s r * ((k + 1 : ℝ) ^ s / productPolydiskConstant s) := by
  have hC := productPolydiskConstant_pos s
  have hterm (ij : productNumeratorIndex s) :
      ‖if (ij.val.1 : ℕ) ≤ k ∧ (ij.val.2 : ℕ) ≤ n then
        r ij * productUpperCoefficient s (k - ij.val.1) (n - ij.val.2) else 0‖ ≤
      ‖r ij‖ * ((k + 1 : ℝ) ^ s / productPolydiskConstant s) := by
    split_ifs with h
    · rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hbase : (((k - (ij.val.1 : ℕ) : ℕ) : ℝ) + 1) ≤ (k + 1 : ℝ) := by
        exact_mod_cast Nat.add_le_add_right (Nat.sub_le k (ij.val.1 : ℕ)) 1
      have hp := pow_le_pow_left₀
        (by positivity : (0 : ℝ) ≤ ((k - (ij.val.1 : ℕ) : ℕ) : ℝ) + 1) hbase s
      exact (productUpperCoefficient_norm_le s _ _).trans
        ((div_le_div_iff_of_pos_right hC).mpr hp)
    · simp only [norm_zero]
      positivity
  calc
    _ ≤ ∑ ij : productNumeratorIndex s,
        ‖if (ij.val.1 : ℕ) ≤ k ∧ (ij.val.2 : ℕ) ≤ n then
          r ij * productUpperCoefficient s (k - ij.val.1) (n - ij.val.2) else 0‖ := by
      unfold productSlabUpperCoefficient
      exact norm_sum_le _ _
    _ ≤ ∑ ij : productNumeratorIndex s,
        ‖r ij‖ * ((k + 1 : ℝ) ^ s / productPolydiskConstant s) :=
      Finset.sum_le_sum (fun ij _ => hterm ij)
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem productSlabPolynomial_norm_le (s : ℕ) (r : productNumeratorIndex s → ℂ)
    {Z W : ℂ} (hZ : ‖Z‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    ‖productSlabPolynomial s r Z W‖ ≤ productSlabCoefficientBound s r := by
  have hterm (ij : productNumeratorIndex s) :
      ‖r ij * Z ^ (ij.val.1 : ℕ) * W ^ (ij.val.2 : ℕ)‖ ≤ ‖r ij‖ := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    have hz : ‖Z‖ ^ (ij.val.1 : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg Z) hZ
    have hw : ‖W‖ ^ (ij.val.2 : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg W) hW
    calc
      _ ≤ (‖r ij‖ * 1) * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hz (norm_nonneg _)) hw
        (pow_nonneg (norm_nonneg _) _) (by positivity)
      _ = _ := by ring
  unfold productSlabPolynomial productSlabCoefficientBound
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ij _ => hterm ij))

end

end MeyerGeneralProblem.StrongParity
