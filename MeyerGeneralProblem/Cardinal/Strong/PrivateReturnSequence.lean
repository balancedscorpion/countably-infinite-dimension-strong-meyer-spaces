module

public import MeyerGeneralProblem.Cardinal.Strong.ReturnRoots
public import MeyerGeneralProblem.Cardinal.Strong.QuarterPhase

@[expose] public section

/-! Actual nearby roots are chosen from the literal arithmetic returns
after a fixed shift by five. That explicit shift makes every return
error small enough for the proved IVT and preserves escape to infinity. -/

namespace MeyerGeneralProblem.StrongParity

open Filter
open scoped Topology

noncomputable section

/-- The literal original quarter-return error, after a fixed explicit shift. -/
def privateReturnError (n : ℕ) : ℝ :=
  beta * quarterN (n + 5) - quarterM (n + 5) - 1 / 4

theorem privateReturn_denominator_lower (n : ℕ) : 8 ≤ |(quarterN (n + 5) : ℝ)| := by
  have hpow : 32 ≤ denominator 6 := by simpa using denominator_ge_two_pow 5
  have hmono : denominator 6 ≤ denominator (n + 6) :=
    denominator_monotone (by omega)
  have hQ : denominator (n + 6) ≤ quarterQ (n + 5) := by
    simpa only [Nat.add_assoc] using (quarterQ_bounds (n + 5)).1
  have hfour : (4 : ℝ) * |(quarterN (n + 5) : ℝ)| = quarterQ (n + 5) := by
    rw [← Int.cast_abs, quarterN_abs]
    exact_mod_cast quarterQ_div_mul_four (n + 5)
  have h32 : (32 : ℝ) ≤ quarterQ (n + 5) := by exact_mod_cast hpow.trans (hmono.trans hQ)
  linarith

theorem privateReturnError_abs_le (n : ℕ) :
    |privateReturnError n| ≤ 1 / |(quarterN (n + 5) : ℝ)| := quarterPhase_error (n + 5)

theorem privateReturnError_small (n : ℕ) : |privateReturnError n| ≤ 1 / 6 := by
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8)
    (privateReturn_denominator_lower n)
  exact (privateReturnError_abs_le n).trans (h.trans (by norm_num))

theorem privateReturn_abs_tendsto_atTop :
    Tendsto (fun n => |(quarterN (n + 5) : ℝ)|) atTop atTop :=
  quarterN_abs_tendsto_atTop.comp (tendsto_add_atTop_nat 5)

theorem privateReturnError_abs_tendsto_zero :
    Tendsto (fun n => |privateReturnError n|) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => abs_nonneg (privateReturnError n)) privateReturnError_abs_le
  simpa only [Function.comp_def, one_div] using
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp privateReturn_abs_tendsto_atTop

/-- The actual original sheet return, chosen from the proved small-error interval. -/
def privateSheetRoot (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : ℝ :=
  Classical.choose (exists_sheet_root_near_return ha (quarterN (n + 5))
    (quarterM (n + 5)) (privateReturnError_small n))

theorem privateSheetRoot_is_root (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    sheetFlow a (privateSheetRoot a ha n) = 0 :=
  (Classical.choose_spec (exists_sheet_root_near_return ha (quarterN (n + 5))
    (quarterM (n + 5)) (privateReturnError_small n))).1

theorem privateSheetRoot_distance (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    |privateSheetRoot a ha n - (quarterN (n + 5) : ℝ)| ≤ |privateReturnError n| :=
  (Classical.choose_spec (exists_sheet_root_near_return ha (quarterN (n + 5))
    (quarterM (n + 5)) (privateReturnError_small n))).2

/-- The actual chosen roots escape, with a uniform lower comparison. -/
theorem privateSheetRoot_abs_lower (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    |(quarterN (n + 5) : ℝ)| - 1 ≤ |privateSheetRoot a ha n| := by
  have htriangle : |(quarterN (n + 5) : ℝ)| ≤
      |privateSheetRoot a ha n| + |privateSheetRoot a ha n - (quarterN (n + 5) : ℝ)| := by
    have h := abs_sub (privateSheetRoot a ha n)
      (privateSheetRoot a ha n - (quarterN (n + 5) : ℝ))
    simpa only [sub_sub_cancel] using h
  have hdist := (privateSheetRoot_distance a ha n).trans (privateReturnError_small n)
  linarith

theorem privateSheetRoot_abs_tendsto_atTop (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n => |privateSheetRoot a ha n|) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [privateReturn_abs_tendsto_atTop.eventually_ge_atTop (b + 1)] with n hn
  linarith [privateSheetRoot_abs_lower a ha n]

end

end MeyerGeneralProblem.StrongParity
