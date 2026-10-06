module

public import MeyerGeneralProblem.Cardinal.Strong.SheetRootPhase
public import MeyerGeneralProblem.Cardinal.Strong.RationalPi

@[expose] public section

/-! Actual uniform denominator and derivative bounds on the FINAL compact slots.
These discharge analytic arithmetic bounds for safe composition. They do not
yet provide sine/cosine, parameter or complete phase/root evaluation algorithms.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The literal phase denominator is uniformly bounded away from zero. -/
theorem sheetLiftDenominator_compact_lower {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (t : ℝ) :
    1 / 2 ≤ sheetLiftDenominator a t := by
  have h := mul_le_mul_of_nonneg_left (Real.cos_le_one (2 * Real.pi * t)) ha
  dsimp [sheetLiftDenominator]
  nlinarith

/-- The actual arctangent argument stays inside the fixed unit interval. -/
theorem sheetLiftTangent_compact_abs_le_one {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (t : ℝ) :
    |sheetLiftTangent a t| ≤ 1 := by
  have hl := sheetLiftDenominator_compact_lower ha ha2 t
  have hd : 0 < sheetLiftDenominator a t := by linarith
  have hy : |a * Real.sin (2 * Real.pi * t)| ≤ a := by
    rw [abs_mul, abs_of_nonneg ha]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (2 * Real.pi * t)) ha
  rw [sheetLiftTangent, abs_div, abs_of_pos hd]
  apply (div_le_one hd).mpr
  linarith

/-- The original circle speed has fixed uniform bounds on every final compact slot. -/
theorem sheetLiftSpeed_compact_bounds {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (t : ℝ) :
    1 / 3 ≤ sheetLiftSpeed a t ∧ sheetLiftSpeed a t ≤ 3 := by
  let D := 1 - 2 * a * Real.cos (2 * Real.pi * t) + a ^ 2
  have hc := Real.cos_le_one (2 * Real.pi * t)
  have hc' := Real.neg_one_le_cos (2 * Real.pi * t)
  have hl : (1 - a) ^ 2 ≤ D := by
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_left hc ha]
  have hu : D ≤ (1 + a) ^ 2 := by
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_left hc' ha]
  have hd : 0 < D := by nlinarith
  have hprod := mul_nonneg (by linarith : 0 ≤ 1 - a) (by linarith : 0 ≤ 1 - 2 * a)
  have hprod' := mul_nonneg (by linarith : 0 ≤ 1 + a) (by linarith : 0 ≤ 1 - 2 * a)
  change 1 / 3 ≤ (1 - a ^ 2) / D ∧ (1 - a ^ 2) / D ≤ 3
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    nlinarith

/-- The original root equation has a concrete uniform derivative bound. -/
theorem sheetRootPhase_compact_deriv_bounds {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (x : ℝ) :
    1 < deriv (sheetRootPhase a) x ∧ deriv (sheetRootPhase a) x < 13 := by
  have ha1 : a < 1 := by linarith
  have hb := beta_between_three_four
  have hs := sheetLiftSpeed_compact_bounds ha ha2 (beta * x - 1 / 4)
  refine ⟨sheetRootPhase_deriv_gt_one ha ha1 x, ?_⟩
  rw [(sheetRootPhase_hasDerivAt ha ha1 x).deriv]
  have hm := mul_le_mul_of_nonneg_left hs.2 (by linarith : 0 ≤ beta)
  nlinarith

end

end MeyerGeneralProblem.StrongParity
