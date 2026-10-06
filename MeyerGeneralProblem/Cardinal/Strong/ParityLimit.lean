module

public import MeyerGeneralProblem.Cardinal.Strong.ParityContinuants
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic

@[expose] public section

/-!
# The real number from the parity continuants

The limit is constructed from the determinant increments of the explicit
recurrence. Its convergence and approximation bound are proved here. This
construction does not assume the existence of a real number with prescribed
continued-fraction coefficients.
-/

namespace MeyerGeneralProblem.StrongParity

open Finset Filter
open scoped Topology

noncomputable section

/-- The rational continuant, regarded as a real number. -/
def convergent (n : ℕ) : ℝ := numerator n / denominator n

/-- The positive magnitude of the adjacent-convergent difference. -/
def increment (n : ℕ) : ℝ := 1 / ((denominator n : ℝ) * denominator (n + 1))

theorem increment_pos (n : ℕ) : 0 < increment n := by
  unfold increment
  positivity [denominator_pos n, denominator_pos (n + 1)]

theorem increment_antitone : Antitone increment := by
  intro n m hnm
  unfold increment
  apply one_div_le_one_div_of_le
  · positivity [denominator_pos n, denominator_pos (n + 1)]
  · gcongr
    · exact_mod_cast denominator_monotone hnm
    · exact_mod_cast denominator_monotone (Nat.add_le_add_right hnm 1)

theorem increment_strictAntitone : StrictAnti increment := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have hq : (0 : ℝ) < denominator (n + 1) := by
    exact_mod_cast denominator_pos (n + 1)
  have hg := denominator_succ_double n
  have hm := denominator_monotone (Nat.le_succ n)
  change denominator n ≤ denominator (n + 1) at hm
  have hstep : (denominator n : ℝ) < denominator (n + 2) := by
    exact_mod_cast (show denominator n < denominator (n + 2) by omega)
  unfold increment
  apply one_div_lt_one_div_of_lt
  · positivity [denominator_pos n, denominator_pos (n + 1)]
  · nlinarith

theorem increment_le_geometric (n : ℕ) : increment n ≤ (1 / 2 : ℝ) ^ n := by
  have hq : (1 : ℝ) ≤ denominator n := by exact_mod_cast denominator_pos n
  have hnext : (2 : ℝ) ^ n ≤ denominator (n + 1) := by
    exact_mod_cast denominator_ge_two_pow n
  have hd : (2 : ℝ) ^ n ≤ (denominator n : ℝ) * denominator (n + 1) := by
    nlinarith [show (0 : ℝ) ≤ denominator (n + 1) by positivity]
  calc
    increment n ≤ 1 / (2 : ℝ) ^ n :=
      one_div_le_one_div_of_le (by positivity) hd
    _ = (1 / 2 : ℝ) ^ n := by rw [one_div_pow]

theorem increment_summable : Summable increment := by
  exact Summable.of_nonneg_of_le (fun n => (increment_pos n).le)
    increment_le_geometric (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem convergent_succ_sub (n : ℕ) :
    convergent (n + 1) - convergent n = (-1 : ℝ) ^ n * increment n := by
  have hd := continuantPair_determinant n
  change (numerator (n + 1) : ℤ) * denominator n -
    (numerator n : ℤ) * denominator (n + 1) = (-1 : ℤ) ^ n at hd
  have hdReal : (numerator (n + 1) : ℝ) * denominator n -
      (numerator n : ℝ) * denominator (n + 1) = (-1 : ℝ) ^ n := by
    exact_mod_cast hd
  have hq : (denominator n : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_pos n).ne'
  have hnext : (denominator (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_pos (n + 1)).ne'
  unfold convergent increment
  field_simp
  nlinarith [hdReal]

theorem convergent_eq_partial_sum (n : ℕ) :
    convergent n = 3 + ∑ i ∈ range n, (-1 : ℝ) ^ i * increment i := by
  induction n with
  | zero => norm_num [convergent, numerator, denominator, continuantPair]
  | succ n ih =>
      rw [sum_range_succ]
      have hd := convergent_succ_sub n
      linarith

/-- The actual real number determined by the explicit parity recurrence. -/
def beta : ℝ := 3 + ∑' n : ℕ, (-1 : ℝ) ^ n * increment n

theorem convergent_tendsto_beta : Tendsto convergent atTop (𝓝 beta) := by
  have hconv : convergent = (fun n =>
      3 + ∑ i ∈ range n, (-1 : ℝ) ^ i * increment i) :=
    funext convergent_eq_partial_sum
  rw [hconv]
  exact tendsto_const_nhds.add increment_summable.tendsto_alternating_series_tsum

/-- The full-sequence error estimate used before restricting to even indices. -/
theorem beta_sub_convergent_abs_le (n : ℕ) :
    |beta - convergent n| ≤ 1 / ((denominator n : ℝ) * denominator (n + 1)) := by
  have h := alternating_series_error_bound increment increment_antitone increment_summable n
  simpa only [beta, convergent_eq_partial_sum, add_sub_add_left_eq_sub, increment] using h

/-- The coefficient error bound has the original denominators. -/
theorem denominator_mul_beta_sub_numerator_abs_le (n : ℕ) :
    |(denominator n : ℝ) * beta - numerator n| ≤ 1 / denominator (n + 1) := by
  have h := beta_sub_convergent_abs_le n
  have hq : (0 : ℝ) < denominator n := by exact_mod_cast denominator_pos n
  have hnext : (0 : ℝ) < denominator (n + 1) := by
    exact_mod_cast denominator_pos (n + 1)
  have hid : (denominator n : ℝ) * beta - numerator n =
      (denominator n : ℝ) * (beta - convergent n) := by
    unfold convergent
    field_simp
  rw [hid, abs_mul, abs_of_pos hq]
  calc
    _ ≤ (denominator n : ℝ) *
        (1 / ((denominator n : ℝ) * denominator (n + 1))) :=
      mul_le_mul_of_nonneg_left h hq.le
    _ = 1 / denominator (n + 1) := by field_simp

theorem denominator_succ_tendsto_atTop :
    Tendsto (fun n => (denominator (n + 1) : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun n => by exact_mod_cast denominator_ge_two_pow n)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

/-- The original coefficient errors decay faster than every fixed inverse
power, along the full sequence after its initial denominator. -/
theorem scaled_coefficient_error_tendsto_zero (m : ℕ) :
    Tendsto (fun n => (denominator (n + 1) : ℝ) ^ m *
      |(denominator (n + 1) : ℝ) * beta - numerator (n + 1)|) atTop (𝓝 0) := by
  have hupper : ∀ᶠ n in atTop,
      (denominator (n + 1) : ℝ) ^ m *
          |(denominator (n + 1) : ℝ) * beta - numerator (n + 1)| ≤
        1 / denominator (n + 1) := by
    filter_upwards [eventually_ge_atTop m] with n hn
    have hq : (1 : ℝ) ≤ denominator (n + 1) := by
      exact_mod_cast denominator_pos (n + 1)
    have hpos : (0 : ℝ) < denominator (n + 1) := by
      exact_mod_cast denominator_pos (n + 1)
    have hg : 2 * (denominator (n + 1) : ℝ) ^ (n + 3) < denominator (n + 2) := by
      exact_mod_cast denominator_growth n
    have hpow : (denominator (n + 1) : ℝ) ^ (m + 1) ≤
        (denominator (n + 1) : ℝ) ^ (n + 3) :=
      pow_le_pow_right₀ hq (by omega)
    have hden : (denominator (n + 1) : ℝ) ^ (m + 1) ≤ denominator (n + 2) := by
      nlinarith [pow_pos hpos (n + 3)]
    calc
      _ ≤ (denominator (n + 1) : ℝ) ^ m * (1 / denominator (n + 2)) :=
        mul_le_mul_of_nonneg_left (denominator_mul_beta_sub_numerator_abs_le (n + 1))
          (by positivity)
      _ ≤ (denominator (n + 1) : ℝ) ^ m *
          (1 / (denominator (n + 1) : ℝ) ^ (m + 1)) := by
        gcongr
      _ = 1 / denominator (n + 1) := by rw [pow_succ]; field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_nhds.div_atTop denominator_succ_tendsto_atTop) _ hupper
  exact Eventually.of_forall (fun n => by positivity)

/-- Even continuants are lower bounds for this constructed limit. -/
theorem convergent_even_le_beta (n : ℕ) : convergent (2 * n) ≤ beta := by
  have h := increment_antitone.alternating_series_le_tendsto
    increment_summable.tendsto_alternating_series_tsum n
  rw [convergent_eq_partial_sum]
  simpa only [beta, add_comm] using add_le_add_left h 3

/-- Odd continuants are upper bounds for this constructed limit. -/
theorem beta_le_convergent_odd (n : ℕ) : beta ≤ convergent (2 * n + 1) := by
  have h := increment_antitone.tendsto_le_alternating_series
    increment_summable.tendsto_alternating_series_tsum n
  rw [convergent_eq_partial_sum]
  simpa only [beta, add_comm] using add_le_add_left h 3

theorem convergent_add_two_sub (n : ℕ) :
    convergent (n + 2) - convergent n =
      (-1 : ℝ) ^ n * (increment n - increment (n + 1)) := by
  calc
    _ = (convergent (n + 2) - convergent (n + 1)) +
        (convergent (n + 1) - convergent n) := by ring
    _ = _ := by
      rw [convergent_succ_sub (n + 1), convergent_succ_sub n, pow_succ]
      ring

theorem convergent_even_lt_beta (n : ℕ) : convergent (2 * n) < beta := by
  have hdiff := convergent_add_two_sub (2 * n)
  have hinc := increment_strictAntitone (Nat.lt_succ_self (2 * n))
  have hnext := convergent_even_le_beta (n + 1)
  rw [show 2 * (n + 1) = 2 * n + 2 by omega] at hnext
  simp only [pow_mul, neg_one_sq, one_pow, one_mul] at hdiff
  linarith

theorem beta_lt_convergent_odd (n : ℕ) : beta < convergent (2 * n + 1) := by
  have hdiff := convergent_add_two_sub (2 * n + 1)
  have hinc := increment_strictAntitone (Nat.lt_succ_self (2 * n + 1))
  have hnext := beta_le_convergent_odd (n + 1)
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega] at hnext
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul, neg_one_mul]
    at hdiff
  linarith

theorem beta_ne_convergent (n : ℕ) : beta ≠ convergent n := by
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp h
    exact (convergent_even_lt_beta k).ne'
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp h
    exact (beta_lt_convergent_odd k).ne

/-- The recurrence constructs a Liouville number, without a real parameter
hypothesis. Its rational approximants are the original continuants. -/
theorem beta_liouville : Liouville beta := by
  intro m
  refine ⟨numerator (m + 2), denominator (m + 2), ?_, ?_, ?_⟩
  · have hbase : 1 < denominator 2 := by norm_num [denominator, continuantPair]
    exact_mod_cast hbase.trans_le (denominator_monotone (show 2 ≤ m + 2 by omega))
  · simpa only [Int.cast_natCast, convergent] using beta_ne_convergent (m + 2)
  · simp only [Int.cast_natCast]
    have hq : (1 : ℝ) ≤ denominator (m + 2) := by
      exact_mod_cast denominator_pos (m + 2)
    have hp : (0 : ℝ) < denominator (m + 2) := by
      exact_mod_cast denominator_pos (m + 2)
    have hnext : (0 : ℝ) < denominator (m + 3) := by
      exact_mod_cast denominator_pos (m + 3)
    have hg : 2 * (denominator (m + 2) : ℝ) ^ (m + 4) < denominator (m + 3) := by
      exact_mod_cast denominator_growth (m + 1)
    have hpow : (denominator (m + 2) : ℝ) ^ m ≤
        (denominator (m + 2) : ℝ) ^ (m + 4) :=
      pow_le_pow_right₀ hq (by omega)
    have hprod : (denominator (m + 2) : ℝ) ^ m <
        (denominator (m + 2) : ℝ) * denominator (m + 3) := by
      nlinarith [pow_pos hp (m + 4)]
    exact (beta_sub_convergent_abs_le (m + 2)).trans_lt
      (one_div_lt_one_div_of_lt (by positivity) hprod)

theorem beta_irrational : Irrational beta := beta_liouville.irrational

/-- The real limit is strictly inside the same interval as the analytic source. -/
theorem beta_between_three_four : 3 < beta ∧ beta < 4 := by
  have hlo := convergent_even_le_beta 1
  have hhi := beta_le_convergent_odd 1
  norm_num [convergent, numerator, denominator, continuantPair] at hlo hhi
  constructor <;> linarith

end

end MeyerGeneralProblem.StrongParity
