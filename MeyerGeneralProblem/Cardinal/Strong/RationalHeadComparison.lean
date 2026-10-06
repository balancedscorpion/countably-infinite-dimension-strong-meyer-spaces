module

public import MeyerGeneralProblem.Cardinal.Strong.RationalBetaApprox
public import MeyerGeneralProblem.Cardinal.Strong.SpectralCone
public import Mathlib.Data.Nat.Find

@[expose] public section

/-! Ordinary rational decisions of the actual original finite spectral head.
The zero beta coefficient is decided exactly. Every nonzero coefficient has
an irrational frequency, so strict rational interval search terminates. -/

namespace MeyerGeneralProblem.StrongParity

open Filter
open scoped Topology

/-- Ordinary rational approximation to an original positive cone frequency. -/
def rationalConeFrequencyApprox (k n p : ℕ) : ℚ := k + rationalBetaApprox p * n

/-- Computed interval radius for that cone-frequency approximation. -/
def rationalConeFrequencyRadius (n p : ℕ) : ℚ := n * rationalBinaryRadius p

/-- A strict rational separation certificate on one side of a rational cutoff. -/
def rationalHeadSeparated (k n : ℕ) (b : ℚ) (p : ℕ) : Bool :=
  decide (rationalConeFrequencyApprox k n p + rationalConeFrequencyRadius n p < b ∨
    b < rationalConeFrequencyApprox k n p - rationalConeFrequencyRadius n p)

noncomputable section

/-- Every actual cone-frequency approximation has the full computed interval error. -/
theorem rationalConeFrequencyApprox_error (k n p : ℕ) :
    |(rationalConeFrequencyApprox k n p : ℝ) - positiveConeFrequency (k, n)| ≤
      (rationalConeFrequencyRadius n p : ℝ) := by
  have he := rationalBetaApprox_error p
  have hnorm : (rationalConeFrequencyApprox k n p : ℝ) - positiveConeFrequency (k, n) =
      ((rationalBetaApprox p : ℝ) - beta) * n := by
    simp only [rationalConeFrequencyApprox, positiveConeFrequency, Rat.cast_add,
      Rat.cast_mul, Rat.cast_natCast]
    ring
  rw [hnorm, abs_mul, show |(n : ℝ)| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
  have h := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg n)
  simpa only [rationalConeFrequencyRadius, Rat.cast_mul, Rat.cast_natCast,
    rationalBinaryRadius_cast, mul_comm] using h

/-- The strict rational certificate has its literal real interval meaning. -/
theorem rationalHeadSeparated_spec (k n : ℕ) (b : ℚ) (p : ℕ) :
    rationalHeadSeparated k n b p = true ↔
      (rationalConeFrequencyApprox k n p : ℝ) + (rationalConeFrequencyRadius n p : ℝ) < (b : ℝ) ∨
      (b : ℝ) < (rationalConeFrequencyApprox k n p : ℝ) - (rationalConeFrequencyRadius n p : ℝ) := by
  simp only [rationalHeadSeparated, decide_eq_true_eq]
  exact_mod_cast (Iff.rfl :
    (rationalConeFrequencyApprox k n p + rationalConeFrequencyRadius n p < b ∨
      b < rationalConeFrequencyApprox k n p - rationalConeFrequencyRadius n p) ↔ _)

/-- A nonzero beta coefficient cannot put an original frequency on any rational boundary. -/
theorem positiveConeFrequency_ne_rat (k n : ℕ) (hn : n ≠ 0) (b : ℚ) :
    positiveConeFrequency (k, n) ≠ (b : ℝ) := by
  have hi := (beta_irrational.mul_natCast hn).add_ratCast (k : ℚ)
  have h := hi.ne_rat b
  simpa only [positiveConeFrequency, Rat.cast_natCast, add_comm] using h

/-- The ordinary strict interval test eventually succeeds for every nonzero beta coefficient. -/
theorem rationalHeadSeparated_exists (k n : ℕ) (hn : n ≠ 0) (b : ℚ) :
    ∃ p, rationalHeadSeparated k n b p = true := by
  have hr : Tendsto (fun p : ℕ => 1 / (2 : ℝ) ^ p) atTop (𝓝 0) := by
    simpa only [one_div_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
  have ht : Tendsto (fun p : ℕ => 2 * (n : ℝ) * (1 / (2 : ℝ) ^ p)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hr.const_mul (2 * (n : ℝ))
  rcases lt_or_gt_of_ne (positiveConeFrequency_ne_rat k n hn b) with hlt | hgt
  · obtain ⟨p, hp⟩ := (ht.eventually_lt_const (sub_pos.mpr hlt)).exists
    refine ⟨p, (rationalHeadSeparated_spec k n b p).mpr (Or.inl ?_)⟩
    have he := (abs_le.mp (rationalConeFrequencyApprox_error k n p)).2
    have hc : (rationalConeFrequencyRadius n p : ℝ) = (n : ℝ) * (1 / (2 : ℝ) ^ p) := by
      simp only [rationalConeFrequencyRadius, Rat.cast_mul, Rat.cast_natCast, rationalBinaryRadius_cast]
    rw [hc] at he ⊢
    linarith
  · obtain ⟨p, hp⟩ := (ht.eventually_lt_const (sub_pos.mpr hgt)).exists
    refine ⟨p, (rationalHeadSeparated_spec k n b p).mpr (Or.inr ?_)⟩
    have he := (abs_le.mp (rationalConeFrequencyApprox_error k n p)).1
    have hc : (rationalConeFrequencyRadius n p : ℝ) = (n : ℝ) * (1 / (2 : ℝ) ^ p) := by
      simp only [rationalConeFrequencyRadius, Rat.cast_mul, Rat.cast_natCast, rationalBinaryRadius_cast]
    rw [hc] at he ⊢
    linarith

end

/-- Ordinary sequential precision search; irrationality pays termination internally. -/
def rationalHeadComparisonPrecision (k n : ℕ) (hn : n ≠ 0) (b : ℚ) : ℕ :=
  Nat.find (rationalHeadSeparated_exists k n hn b)

/-- Ordinary exact decision of an original cone frequency's membership in a rational head. -/
def rationalHeadContains (k n : ℕ) (b : ℚ) : Bool :=
  if hn : n = 0 then decide ((k : ℚ) ≤ b)
  else let p := rationalHeadComparisonPrecision k n hn b
    decide (rationalConeFrequencyApprox k n p + rationalConeFrequencyRadius n p < b)

noncomputable section

/-- The implemented precision search always reaches a strict interval certificate. -/
theorem rationalHeadComparisonPrecision_success (k n : ℕ) (hn : n ≠ 0) (b : ℚ) :
    rationalHeadSeparated k n b (rationalHeadComparisonPrecision k n hn b) = true :=
  Nat.find_spec (rationalHeadSeparated_exists k n hn b)

/-- The ordinary Boolean decision is equivalent to the ACTUAL complete head inequality. -/
theorem rationalHeadContains_iff (k n : ℕ) (b : ℚ) :
    rationalHeadContains k n b = true ↔ positiveConeFrequency (k, n) ≤ (b : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp only [rationalHeadContains, ↓reduceDIte, decide_eq_true_eq,
      positiveConeFrequency, Nat.cast_zero, mul_zero, add_zero]
    exact_mod_cast (Iff.rfl : (k : ℚ) ≤ b ↔ _)
  · simp only [rationalHeadContains, dite_eq_right hn, decide_eq_true_eq]
    let p := rationalHeadComparisonPrecision k n hn b
    have hsep := (rationalHeadSeparated_spec k n b p).mp
      (rationalHeadComparisonPrecision_success k n hn b)
    have he := abs_le.mp (rationalConeFrequencyApprox_error k n p)
    have hreal : ((rationalConeFrequencyApprox k n p : ℝ) +
        (rationalConeFrequencyRadius n p : ℝ) < (b : ℝ)) ↔
        positiveConeFrequency (k, n) ≤ (b : ℝ) := by
      constructor
      · intro h; linarith [he.1]
      · intro h
        rcases hsep with hlo | hhi
        · exact hlo
        · exfalso; linarith [he.2]
    exact_mod_cast hreal

end

end MeyerGeneralProblem.StrongParity
