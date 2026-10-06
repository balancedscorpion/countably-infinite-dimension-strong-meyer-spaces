module

public import MeyerGeneralProblem.Cardinal.Strong.FiniteComplexBounds

@[expose] public section

/-! Ordinary rational complex powers and full power/product perturbation
budgets for the original two-variable slab. -/

namespace MeyerGeneralProblem.StrongParity

/-- Ordinary finite rational-coordinate power. -/
def rationalComplexPow (q : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => rationalComplexMul q (rationalComplexPow q n)

/-- Computed power sensitivity for two complex arguments of norm at most two. -/
def finiteComplexPowerSensitivity (n : ℕ) : ℕ := n * 2 ^ n

noncomputable section

/-- The rational power program has the exact literal complex power value. -/
theorem rationalComplexPow_value (q : ℚ × ℚ) (n : ℕ) :
    rationalComplexValue (rationalComplexPow q n) = rationalComplexValue q ^ n := by
  induction n with
  | zero => simp [rationalComplexPow, rationalComplexValue]
  | succ n ih => rw [rationalComplexPow, rationalComplexMul_value, ih, pow_succ']

/-- Safe norm bounds for every finite power of a bounded complex argument. -/
theorem complexPow_norm_le_two_pow {z : ℂ} (hz : ‖z‖ ≤ 2) (n : ℕ) :
    ‖z ^ n‖ ≤ (2 : ℝ) ^ n := by
  rw [norm_pow]
  gcongr

/-- Product perturbation retaining BOTH explicit factor-error budgets. -/
theorem complexProduct_scaled_errors {a b x y : ℂ} (M B La Lb : ℕ)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (ha : ‖a‖ ≤ (M : ℝ)) (hy : ‖y‖ ≤ (B : ℝ))
    (hab : ‖a - b‖ ≤ (La : ℝ) * epsilon) (hxy : ‖x - y‖ ≤ (Lb : ℝ) * epsilon) :
    ‖a * x - b * y‖ ≤ ((M * Lb + La * B : ℕ) : ℝ) * epsilon := by
  calc
    _ = ‖a * (x - y) + (a - b) * y‖ := by congr 1; ring
    _ ≤ ‖a * (x - y)‖ + ‖(a - b) * y‖ := norm_add_le _ _
    _ = ‖a‖ * ‖x - y‖ + ‖a - b‖ * ‖y‖ := by rw [norm_mul, norm_mul]
    _ ≤ (M : ℝ) * ((Lb : ℝ) * epsilon) + ((La : ℝ) * epsilon) * (B : ℝ) :=
      add_le_add (mul_le_mul ha hxy (norm_nonneg _) (Nat.cast_nonneg M))
        (mul_le_mul hab hy (norm_nonneg _) (by positivity))
    _ = _ := by push_cast; ring

/-- Every finite power has an explicit integer perturbation bound. -/
theorem complexPow_sub_norm_le {a b : ℂ} (ha : ‖a‖ ≤ 2) (hb : ‖b‖ ≤ 2)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hab : ‖a - b‖ ≤ epsilon) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ (finiteComplexPowerSensitivity n : ℝ) * epsilon := by
  induction n with
  | zero => simp [finiteComplexPowerSensitivity]
  | succ n ih =>
    rw [pow_succ', pow_succ']
    have h := complexProduct_sub_norm_le 2 (2 ^ n) (finiteComplexPowerSensitivity n)
      epsilon he ha (by simpa using complexPow_norm_le_two_pow hb n) hab ih
    have hL : 2 ^ n + 2 * finiteComplexPowerSensitivity n ≤ finiteComplexPowerSensitivity (n + 1) := by
      simp only [finiteComplexPowerSensitivity, pow_succ]
      nlinarith [Nat.zero_le (2 ^ n)]
    exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hL) he)

/-- BOTH variable powers are retained in the original slab monomial error. -/
theorem complexBivariateMonomial_sub_norm_le {a b u v : ℂ}
    (ha : ‖a‖ ≤ 2) (hb : ‖b‖ ≤ 2) (hu : ‖u‖ ≤ 2) (hv : ‖v‖ ≤ 2)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hab : ‖a - b‖ ≤ epsilon) (huv : ‖u - v‖ ≤ epsilon)
    (k n : ℕ) :
    ‖a ^ k * u ^ n - b ^ k * v ^ n‖ ≤
      (finiteComplexPowerSensitivity (k + n) : ℝ) * epsilon := by
  have h := complexProduct_scaled_errors (2 ^ k) (2 ^ n)
    (finiteComplexPowerSensitivity k) (finiteComplexPowerSensitivity n) epsilon he
    (by simpa using complexPow_norm_le_two_pow ha k)
    (by simpa using complexPow_norm_le_two_pow hv n)
    (complexPow_sub_norm_le ha hb epsilon he hab k)
    (complexPow_sub_norm_le hu hv epsilon he huv n)
  have heq : 2 ^ k * finiteComplexPowerSensitivity n + finiteComplexPowerSensitivity k * 2 ^ n =
      finiteComplexPowerSensitivity (k + n) := by
    simp only [finiteComplexPowerSensitivity, pow_add]
    ring
  simpa only [heq] using h

/-- The natural power budget is monotone in its degree. -/
theorem finiteComplexPowerSensitivity_mono {a b : ℕ} (h : a ≤ b) :
    finiteComplexPowerSensitivity a ≤ finiteComplexPowerSensitivity b := by
  unfold finiteComplexPowerSensitivity
  gcongr <;> norm_num

end

end MeyerGeneralProblem.StrongParity
