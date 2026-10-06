module

public import MeyerGeneralProblem.Cardinal.Strong.RationalUnitPhaseNames
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! A strict Gaussian-rational nonzero test. Its soundness and eventual success
use the full complex binary error, not a floating point determinant threshold. -/

namespace MeyerGeneralProblem.StrongParity

open Filter
open scoped Topology

/-- Ordinary exact rational L1 size, requiring no square root. -/
def rationalComplexL1 (q : ℚ × ℚ) : ℚ := |q.1| + |q.2|

/-- Ordinary strict rational apartness test at the requested binary precision. -/
def rationalComplexApart (q : ℚ × ℚ) (p : ℕ) : Bool :=
  decide (2 * rationalBinaryRadius p < rationalComplexL1 q)

noncomputable section

/-- The rational L1 computation has exactly its literal complex-coordinate value. -/
theorem rationalComplexL1_value (q : ℚ × ℚ) :
    (rationalComplexL1 q : ℝ) = |(rationalComplexValue q).re| + |(rationalComplexValue q).im| := by
  simp [rationalComplexL1, rationalComplexValue]

/-- The Boolean test has its strict real margin meaning. -/
theorem rationalComplexApart_spec (q : ℚ × ℚ) (p : ℕ) :
    rationalComplexApart q p = true ↔
      2 * (1 / (2 : ℝ) ^ p) < |(rationalComplexValue q).re| + |(rationalComplexValue q).im| := by
  simp only [rationalComplexApart, decide_eq_true_eq]
  have h : 2 * rationalBinaryRadius p < rationalComplexL1 q ↔
      (2 : ℝ) * (rationalBinaryRadius p : ℝ) < (rationalComplexL1 q : ℝ) := by
    exact_mod_cast Iff.rfl
  simpa only [rationalBinaryRadius_cast, rationalComplexL1_value] using h

/-- A passing exact rational margin certifies the ACTUAL complex value is nonzero. -/
theorem rationalComplexApart_sound {q : ℚ × ℚ} {z : ℂ} {p : ℕ}
    (he : ‖rationalComplexValue q - z‖ ≤ 1 / (2 : ℝ) ^ p)
    (hp : rationalComplexApart q p = true) : z ≠ 0 := by
  intro hz
  rw [hz, sub_zero] at he
  have h := (rationalComplexApart_spec q p).mp hp
  have hr := Complex.abs_re_le_norm (rationalComplexValue q)
  have hi := Complex.abs_im_le_norm (rationalComplexValue q)
  linarith

/-- EVERY valid binary complex name of a nonzero value eventually passes the
ordinary strict rational test. The precision witness is proved internally. -/
theorem rationalComplexApart_eventually (name : ℕ → ℚ × ℚ) {z : ℂ}
    (he : ∀ p, ‖rationalComplexValue (name p) - z‖ ≤ 1 / (2 : ℝ) ^ p) (hz : z ≠ 0) :
    ∀ᶠ p in atTop, rationalComplexApart (name p) p = true := by
  have hr : Tendsto (fun p : ℕ => 1 / (2 : ℝ) ^ p) atTop (𝓝 0) := by
    simpa only [one_div_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
  have ht : Tendsto (fun p : ℕ => 3 * (1 / (2 : ℝ) ^ p)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hr.const_mul 3
  filter_upwards [ht.eventually_lt_const (norm_pos_iff.mpr hz)] with p hp
  apply (rationalComplexApart_spec (name p) p).mpr
  have h := norm_sub_norm_le z (rationalComplexValue (name p))
  rw [norm_sub_rev] at h
  have hn := Complex.norm_le_abs_re_add_abs_im (rationalComplexValue (name p))
  have he' := he p
  linarith

end

end MeyerGeneralProblem.StrongParity
