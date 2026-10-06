module

public import MeyerGeneralProblem.Cardinal.Strong.ParityLimit

@[expose] public section

/-!
# Returns to the original quarter phase

The integers are constructed from the actual continuants. The multiplier
and sign are computed by remainders; the return does not replace the
quarter phase with a homogeneous approximation.
-/

namespace MeyerGeneralProblem.StrongParity

open Filter
open scoped Topology

noncomputable section

/-- The positive denominator combination divisible by four. -/
def quarterQ (n : ℕ) : ℕ :=
  quarterMultiplier (denominator n) (denominator (n + 1)) *
    denominator (n + 1) + denominator n

/-- The odd numerator combination paired with `quarterQ`. -/
def quarterP (n : ℕ) : ℕ :=
  quarterMultiplier (denominator n) (denominator (n + 1)) *
    numerator (n + 1) + numerator n

/-- Choose the sign that makes the odd numerator equal to one modulo four. -/
def quarterSign (n : ℕ) : ℤ := if quarterP n % 4 = 1 then 1 else -1

/-- The signed integer denominator of the quarter return. -/
def quarterN (n : ℕ) : ℤ := quarterSign n * (quarterQ n / 4 : ℕ)

/-- The integer part paired with `quarterN`. -/
def quarterM (n : ℕ) : ℤ :=
  if quarterP n % 4 = 1 then (quarterP n / 4 : ℕ)
  else -((quarterP n + 1) / 4 : ℕ)

theorem quarterQ_mod_four (n : ℕ) : quarterQ n % 4 = 0 :=
  quarterMultiplier_denominator_mod_four (denominator_odd n) (denominator_odd (n + 1))

theorem quarterP_odd (n : ℕ) : Odd (quarterP n) := quarter_combination_numerator_odd n

theorem quarterQ_bounds (n : ℕ) :
    denominator (n + 1) ≤ quarterQ n ∧ quarterQ n ≤ 4 * denominator (n + 1) := by
  have hm := denominator_monotone (Nat.le_succ n)
  change denominator n ≤ denominator (n + 1) at hm
  unfold quarterQ
  rcases quarterMultiplier_values (denominator n) (denominator (n + 1)) with h | h
  · rw [h]; omega
  · rw [h]; omega

theorem quarterQ_div_mul_four (n : ℕ) : 4 * (quarterQ n / 4) = quarterQ n := by
  have h := Nat.mod_add_div (quarterQ n) 4
  rw [quarterQ_mod_four] at h
  omega

theorem quarterSign_abs (n : ℕ) : |quarterSign n| = 1 := by
  unfold quarterSign
  split <;> norm_num

theorem quarterN_abs (n : ℕ) : |quarterN n| = (quarterQ n / 4 : ℕ) := by
  rw [quarterN, abs_mul, quarterSign_abs, one_mul, abs_of_nonneg (by positivity)]

theorem quarterN_mul_four (n : ℕ) :
    4 * quarterN n = quarterSign n * quarterQ n := by
  have h : (4 : ℤ) * (quarterQ n / 4 : ℕ) = quarterQ n := by
    exact_mod_cast quarterQ_div_mul_four n
  rw [quarterN]
  calc
    _ = quarterSign n * (4 * (quarterQ n / 4 : ℕ)) := by ring
    _ = _ := by rw [h]

theorem quarterM_mul_four_add_one (n : ℕ) :
    4 * quarterM n + 1 = quarterSign n * quarterP n := by
  have hp := Nat.odd_iff.mp (quarterP_odd n)
  have hdiv := Nat.mod_add_div (quarterP n) 4
  have hdivNext := Nat.mod_add_div (quarterP n + 1) 4
  unfold quarterM quarterSign
  split <;> omega

theorem quarterN_abs_pos (n : ℕ) : 0 < |quarterN n| := by
  rw [quarterN_abs]
  have hpos := denominator_pos (n + 1)
  have hbounds := quarterQ_bounds n
  have hmod := quarterQ_mod_four n
  exact_mod_cast (show 0 < quarterQ n / 4 by omega)

theorem quarterN_abs_le_denominator (n : ℕ) :
    |quarterN n| ≤ (denominator (n + 1) : ℤ) := by
  rw [quarterN_abs]
  have hb := (quarterQ_bounds n).2
  exact_mod_cast (show quarterQ n / 4 ≤ denominator (n + 1) by omega)

/-- These are returns to `1/4` for the constructed `beta`. -/
theorem quarterPhase_error (n : ℕ) :
    |beta * (quarterN n : ℝ) - quarterM n - 1 / 4| ≤
      1 / |(quarterN n : ℝ)| := by
  let r := quarterMultiplier (denominator n) (denominator (n + 1))
  have hN : 4 * (quarterN n : ℝ) = (quarterSign n : ℝ) * quarterQ n := by
    exact_mod_cast quarterN_mul_four n
  have hM : 4 * (quarterM n : ℝ) + 1 = (quarterSign n : ℝ) * quarterP n := by
    exact_mod_cast quarterM_mul_four_add_one n
  have hsign : |(quarterSign n : ℝ)| = 1 := by exact_mod_cast quarterSign_abs n
  have hr : (0 : ℝ) ≤ r ∧ (r : ℝ) ≤ 3 := by
    rcases quarterMultiplier_values (denominator n) (denominator (n + 1)) with h | h
    · change 0 ≤ (quarterMultiplier (denominator n) (denominator (n + 1)) : ℝ) ∧
        (quarterMultiplier (denominator n) (denominator (n + 1)) : ℝ) ≤ 3
      rw [h]; norm_num
    · change 0 ≤ (quarterMultiplier (denominator n) (denominator (n + 1)) : ℝ) ∧
        (quarterMultiplier (denominator n) (denominator (n + 1)) : ℝ) ≤ 3
      rw [h]; norm_num
  have hidentity :
      4 * (beta * (quarterN n : ℝ) - quarterM n - 1 / 4) =
      (quarterSign n : ℝ) *
        ((r : ℝ) * ((denominator (n + 1) : ℝ) * beta - numerator (n + 1)) +
          ((denominator n : ℝ) * beta - numerator n)) := by
    calc
      _ = beta * (4 * (quarterN n : ℝ)) - (4 * (quarterM n : ℝ) + 1) := by ring
      _ = beta * ((quarterSign n : ℝ) * quarterQ n) -
          (quarterSign n : ℝ) * quarterP n := by rw [hN, hM]
      _ = _ := by
        change beta * ((quarterSign n : ℝ) *
          ((quarterMultiplier (denominator n) (denominator (n + 1)) *
            denominator (n + 1) + denominator n : ℕ) : ℝ)) -
          (quarterSign n : ℝ) *
            (quarterMultiplier (denominator n) (denominator (n + 1)) *
              numerator (n + 1) + numerator n : ℕ) = _
        simp only [Nat.cast_add, Nat.cast_mul]
        change _ = (quarterSign n : ℝ) *
          ((quarterMultiplier (denominator n) (denominator (n + 1)) : ℝ) *
            ((denominator (n + 1) : ℝ) * beta - numerator (n + 1)) +
              ((denominator n : ℝ) * beta - numerator n))
        ring
  have herror :
      4 * |beta * (quarterN n : ℝ) - quarterM n - 1 / 4| ≤
        3 / denominator (n + 2) + 1 / denominator (n + 1) := by
    calc
      _ = |4 * (beta * (quarterN n : ℝ) - quarterM n - 1 / 4)| := by
        rw [abs_mul]; norm_num
      _ = |(r : ℝ) *
            ((denominator (n + 1) : ℝ) * beta - numerator (n + 1)) +
              ((denominator n : ℝ) * beta - numerator n)| := by
        rw [hidentity, abs_mul, hsign, one_mul]
      _ ≤ |(r : ℝ) *
            ((denominator (n + 1) : ℝ) * beta - numerator (n + 1))| +
              |(denominator n : ℝ) * beta - numerator n| := abs_add_le _ _
      _ ≤ (r : ℝ) * (1 / denominator (n + 2)) + 1 / denominator (n + 1) := by
        rw [abs_mul, abs_of_nonneg hr.1]
        gcongr
        · exact denominator_mul_beta_sub_numerator_abs_le (n + 1)
        · exact denominator_mul_beta_sub_numerator_abs_le n
      _ ≤ _ := by
        simp only [div_eq_mul_inv, one_mul]
        gcongr
        exact hr.2
  have hq : (0 : ℝ) < denominator (n + 1) := by exact_mod_cast denominator_pos (n + 1)
  have hm : (denominator (n + 1) : ℝ) ≤ denominator (n + 2) := by
    exact_mod_cast denominator_monotone (show n + 1 ≤ n + 2 by omega)
  have hrecip : 1 / (denominator (n + 2) : ℝ) ≤ 1 / denominator (n + 1) :=
    one_div_le_one_div_of_le hq hm
  have hNpos : (0 : ℝ) < |(quarterN n : ℝ)| := by exact_mod_cast quarterN_abs_pos n
  have hNbound : |(quarterN n : ℝ)| ≤ denominator (n + 1) := by
    exact_mod_cast quarterN_abs_le_denominator n
  apply le_trans _ (one_div_le_one_div_of_le hNpos hNbound)
  have hthree : 3 / (denominator (n + 2) : ℝ) =
      3 * (1 / denominator (n + 2)) := by ring
  rw [hthree] at herror
  linarith

/-- The actual return denominators escape every bounded interval. -/
theorem quarterN_abs_tendsto_atTop :
    Tendsto (fun n => |(quarterN n : ℝ)|) atTop atTop := by
  have hscale := denominator_succ_tendsto_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 4)
  apply tendsto_atTop_mono _ hscale
  intro n
  have hfour : (4 : ℝ) * |(quarterN n : ℝ)| = quarterQ n := by
    rw [← Int.cast_abs, quarterN_abs]
    exact_mod_cast quarterQ_div_mul_four n
  have hbound : (denominator (n + 1) : ℝ) ≤ quarterQ n := by
    exact_mod_cast (quarterQ_bounds n).1
  linarith

end

end MeyerGeneralProblem.StrongParity
