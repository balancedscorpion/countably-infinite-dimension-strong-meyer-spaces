module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginalFiniteCoefficients

@[expose] public section

/-! Explicit finite size and perturbation bounds for the complete original
single-sheet coefficient recurrence. The budgets use natural arithmetic only. -/

namespace MeyerGeneralProblem.StrongParity

/-- Explicit finite size budget for the proved sheet recurrence. -/
def sheetFiniteWCoefficientSize : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | k + 1, n + 1 => sheetFiniteWCoefficientSize (k + 1) n +
      sheetFiniteWCoefficientSize k n + sheetFiniteWCoefficientSize k (n + 1)
termination_by k n => (k, n)

/-- Finite sensitivity budget, with the true recurrence dependencies. -/
def sheetFiniteWCoefficientSensitivity : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, 0 => k + 1
  | k + 1, n + 1 => sheetFiniteWCoefficientSize (k + 1) n +
      sheetFiniteWCoefficientSensitivity (k + 1) n +
      sheetFiniteWCoefficientSensitivity k n + sheetFiniteWCoefficientSize k (n + 1) +
      sheetFiniteWCoefficientSensitivity k (n + 1)
termination_by k n => (k, n)

theorem real_bounded_mul_perturbation {a b x y B L epsilon : ℝ}
    (ha : |a| ≤ 1) (hxy : |x - y| ≤ L * epsilon)
    (hab : |a - b| ≤ epsilon) (hy : |y| ≤ B)
    :
    |a * x - b * y| ≤ (L + B) * epsilon := by
  have he : 0 ≤ epsilon := (abs_nonneg _).trans hab
  calc
    _ = |a * (x - y) + (a - b) * y| := by congr 1; ring
    _ ≤ |a * (x - y)| + |(a - b) * y| := abs_add_le _ _
    _ = |a| * |x - y| + |a - b| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (L * epsilon) + epsilon * B :=
      add_le_add (mul_le_mul ha hxy (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
        (mul_le_mul hab hy (abs_nonneg _) he)
    _ = _ := by ring

theorem real_bounded_pow_perturbation {a b epsilon : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (hab : |a - b| ≤ epsilon) (n : ℕ) :
    |a ^ n - b ^ n| ≤ (n : ℝ) * epsilon := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := real_bounded_mul_perturbation ha ih hab
      (by simpa [abs_pow] using pow_le_one₀ (n := n) (abs_nonneg b) hb)
    simpa [pow_succ, abs_pow, mul_comm, Nat.cast_add, Nat.cast_one] using h

theorem sheetFiniteWCoefficient_abs_le_size {a : ℝ} (ha : |a| ≤ 1) (k n : ℕ) :
    |sheetFiniteWCoefficient a k n| ≤ (sheetFiniteWCoefficientSize k n : ℝ) := by
  induction k generalizing n with
  | zero => simpa [sheetFiniteWCoefficient, sheetFiniteWCoefficientSize, abs_pow] using
      pow_le_one₀ (n := n) (abs_nonneg a) ha
  | succ k ih =>
    induction n with
    | zero => simpa [sheetFiniteWCoefficient, sheetFiniteWCoefficientSize, abs_pow] using
        pow_le_one₀ (n := k + 1) (abs_nonneg a) ha
    | succ n ihn =>
      rw [sheetFiniteWCoefficient, sheetFiniteWCoefficientSize]
      push_cast
      calc
        _ ≤ |a * sheetFiniteWCoefficient a (k + 1) n + sheetFiniteWCoefficient a k n| +
            |a * sheetFiniteWCoefficient a k (n + 1)| := by
              simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le
                (a * sheetFiniteWCoefficient a (k + 1) n + sheetFiniteWCoefficient a k n) 0
                (a * sheetFiniteWCoefficient a k (n + 1)))
        _ ≤ |a * sheetFiniteWCoefficient a (k + 1) n| + |sheetFiniteWCoefficient a k n| +
            |a * sheetFiniteWCoefficient a k (n + 1)| := by gcongr; exact abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul, abs_mul]
          have h1 := mul_le_mul ha ihn (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
          have h2 := mul_le_mul ha (ih (n + 1)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
          simpa only [one_mul] using add_le_add (add_le_add h1 (ih n)) h2

/-- Proved perturbation bound for every actual single-sheet coefficient. -/
theorem sheetFiniteWCoefficient_abs_sub_le_sensitivity {a b epsilon : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : |a - b| ≤ epsilon) (k n : ℕ) :
    |sheetFiniteWCoefficient a k n - sheetFiniteWCoefficient b k n| ≤
      (sheetFiniteWCoefficientSensitivity k n : ℝ) * epsilon := by
  induction k generalizing n with
  | zero => simpa [sheetFiniteWCoefficient, sheetFiniteWCoefficientSensitivity] using
      real_bounded_pow_perturbation ha hb hab n
  | succ k ih =>
    induction n with
    | zero =>
      have hneg : |-a - -b| ≤ epsilon := by
        rw [show -a - -b = -(a - b) by ring, abs_neg]
        exact hab
      simpa [sheetFiniteWCoefficient, sheetFiniteWCoefficientSensitivity] using
        real_bounded_pow_perturbation (by simpa using ha) (by simpa using hb) hneg (k + 1)
    | succ n ihn =>
      have h1 := real_bounded_mul_perturbation ha ihn hab
        (sheetFiniteWCoefficient_abs_le_size hb (k + 1) n)
      have h2 := real_bounded_mul_perturbation ha (ih (n + 1)) hab
        (sheetFiniteWCoefficient_abs_le_size hb k (n + 1))
      rw [sheetFiniteWCoefficient, sheetFiniteWCoefficient,
        sheetFiniteWCoefficientSensitivity]
      push_cast
      calc
        _ = |(a * sheetFiniteWCoefficient a (k + 1) n - b * sheetFiniteWCoefficient b (k + 1) n) +
              (sheetFiniteWCoefficient a k n - sheetFiniteWCoefficient b k n) -
              (a * sheetFiniteWCoefficient a k (n + 1) - b * sheetFiniteWCoefficient b k (n + 1))| := by
                congr 1; ring
        _ ≤ |(a * sheetFiniteWCoefficient a (k + 1) n - b * sheetFiniteWCoefficient b (k + 1) n) +
              (sheetFiniteWCoefficient a k n - sheetFiniteWCoefficient b k n)| +
              |a * sheetFiniteWCoefficient a k (n + 1) - b * sheetFiniteWCoefficient b k (n + 1)| := by
                simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le
                  ((a * sheetFiniteWCoefficient a (k + 1) n - b * sheetFiniteWCoefficient b (k + 1) n) +
                    (sheetFiniteWCoefficient a k n - sheetFiniteWCoefficient b k n)) 0
                  (a * sheetFiniteWCoefficient a k (n + 1) - b * sheetFiniteWCoefficient b k (n + 1)))
        _ ≤ (|a * sheetFiniteWCoefficient a (k + 1) n - b * sheetFiniteWCoefficient b (k + 1) n| +
              |sheetFiniteWCoefficient a k n - sheetFiniteWCoefficient b k n|) +
              |a * sheetFiniteWCoefficient a k (n + 1) - b * sheetFiniteWCoefficient b k (n + 1)| := by
                gcongr; exact abs_add_le _ _
        _ ≤ _ := by
          have h := add_le_add (add_le_add h1 (ih n)) h2
          exact h.trans_eq (by ring)

end MeyerGeneralProblem.StrongParity
