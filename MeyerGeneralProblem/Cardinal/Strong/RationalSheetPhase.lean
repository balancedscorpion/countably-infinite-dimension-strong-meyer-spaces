module

public import MeyerGeneralProblem.Cardinal.Strong.RationalSheetTangent
public import MeyerGeneralProblem.Cardinal.Strong.RationalArctanPerturbation

@[expose] public section

/-! The literal original phase is evaluated by finite rational operations. -/

namespace MeyerGeneralProblem.StrongParity

/-- The raw executable original phase value at a fixed internal precision. -/
def rationalSheetPhaseRaw (a t : ℚ) (p : ℕ) : ℚ :=
  t + rationalMagnitudeArctanApprox (rationalSheetTangent a t p) p * rationalInvPiApprox p

/-- A definite internal precision paying the actual angular magnitude. -/
def rationalSheetPhasePrecision (t : ℚ) (p : ℕ) : ℕ := p + rationalMagnitude t + 2

/-- An executable actual original phase approximation with binary precision. -/
def rationalSheetPhaseApprox (a t : ℚ) (p : ℕ) : ℚ :=
  if a = 0 then t else rationalSheetPhaseRaw a t (rationalSheetPhasePrecision t p)

noncomputable section

/-- The computed reciprocal pi is safely bounded at every precision. -/
theorem rationalInvPiApprox_abs_le_third (p : ℕ) : |(rationalInvPiApprox p : ℝ)| ≤ 1 / 3 := by
  have hp : 0 < (rationalPiApprox p : ℝ) := by linarith [rationalPiApprox_gt_three p]
  simp only [rationalInvPiApprox, Rat.cast_inv]
  rw [abs_of_pos (inv_pos.mpr hp), inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith [rationalPiApprox_gt_three p])

/-- The ACTUAL compact-slot arctangent correction is bounded independently of the input. -/
theorem sheetLiftArctan_compact_abs_le_one {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (t : ℝ) :
    |Real.arctan (sheetLiftTangent a t)| ≤ 1 := by
  have h : |Real.arctan (sheetLiftTangent a t)| ≤ |sheetLiftTangent a t| := by
    simpa only [Real.arctan_zero, sub_zero] using arctan_abs_sub_le (sheetLiftTangent a t) 0
  exact h.trans (sheetLiftTangent_compact_abs_le_one ha ha1 t)

/-- Actual error of the computed correction BEFORE applying the definite precision schedule. -/
theorem rationalSheetPhaseRaw_error {a : ℚ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (t : ℚ) (p : ℕ) :
    |(rationalSheetPhaseRaw a t p : ℝ) - sheetPhaseLift a t| ≤
      (2 + 2 * |(t : ℝ)|) / (2 : ℝ) ^ p := by
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha1R : (a : ℝ) ≤ 1 / 2 := by
    have h : (a : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast ha1
    norm_num at h
    exact h
  let y := Real.arctan (sheetLiftTangent (a : ℝ) (t : ℝ))
  let yh := (rationalMagnitudeArctanApprox (rationalSheetTangent a t p) p : ℝ)
  let ih := (rationalInvPiApprox p : ℝ)
  have hy : |y| ≤ 1 := sheetLiftArctan_compact_abs_le_one haR ha1R t
  have hyh : |yh - y| ≤ 1 / (2 : ℝ) ^ p +
      2 * ((1 + 2 * |(t : ℝ)|) / (2 : ℝ) ^ p) :=
    rationalMagnitudeArctanApprox_real_error _ _ (rationalSheetTangent_error ha ha1 t p)
  have hih : |ih| ≤ 1 / 3 := rationalInvPiApprox_abs_le_third p
  have hierror : |ih - Real.pi⁻¹| ≤ 1 / (9 * (2 : ℝ) ^ p) := rationalInvPiApprox_error p
  have hid : (rationalSheetPhaseRaw a t p : ℝ) - sheetPhaseLift a t =
      (yh - y) * ih + y * (ih - Real.pi⁻¹) := by
    simp only [rationalSheetPhaseRaw, Rat.cast_add, Rat.cast_mul, sheetPhaseLift]
    dsimp [yh, y, ih]
    ring
  rw [hid]
  calc
    _ ≤ |yh - y| * |ih| + |y| * |ih - Real.pi⁻¹| := by
      simpa only [abs_mul] using abs_add_le ((yh - y) * ih) (y * (ih - Real.pi⁻¹))
    _ ≤ (1 / (2 : ℝ) ^ p + 2 * ((1 + 2 * |(t : ℝ)|) / (2 : ℝ) ^ p)) * (1 / 3) +
        1 * (1 / (9 * (2 : ℝ) ^ p)) := by
      exact add_le_add (mul_le_mul hyh hih (abs_nonneg _) (by positivity))
        (mul_le_mul hy hierror (abs_nonneg _) (by norm_num))
    _ ≤ _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      norm_num
      have hr : 0 ≤ ((2 : ℝ) ^ p)⁻¹ := by positivity
      nlinarith [mul_nonneg (abs_nonneg (t : ℝ)) hr]

/-- The explicit binary schedule dominates every linear integer magnitude. -/
theorem two_pow_ge_add_one (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

/-- Uniform error of the literal computed original phase at EVERY rational input. -/
theorem rationalSheetPhaseApprox_error {a : ℚ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (t : ℚ) (p : ℕ) :
    |(rationalSheetPhaseApprox a t p : ℝ) - sheetPhaseLift a t| ≤ 1 / (2 : ℝ) ^ p := by
  by_cases ha0 : a = 0
  · simp [rationalSheetPhaseApprox, ha0, sheetPhaseLift_zero_parameter]
  rw [rationalSheetPhaseApprox, ite_eq_right ha0]
  let M := rationalMagnitude t
  have hM : |(t : ℝ)| ≤ (M : ℝ) := rational_abs_le_magnitude t
  have hb : 2 + 2 * M ≤ 2 ^ (M + 2) := by
    rw [pow_add]
    norm_num
    have h := two_pow_ge_add_one M
    omega
  have hbR : (2 : ℝ) + 2 * M ≤ (2 : ℝ) ^ (M + 2) := by exact_mod_cast hb
  calc
    _ ≤ (2 + 2 * |(t : ℝ)|) / (2 : ℝ) ^ rationalSheetPhasePrecision t p :=
      rationalSheetPhaseRaw_error ha ha1 t _
    _ ≤ (2 + 2 * M) / (2 : ℝ) ^ rationalSheetPhasePrecision t p := by gcongr
    _ ≤ (2 : ℝ) ^ (M + 2) / (2 : ℝ) ^ rationalSheetPhasePrecision t p := by gcongr
    _ = _ := by
      dsimp [rationalSheetPhasePrecision, M]
      rw [show p + rationalMagnitude t + 2 = p + (rationalMagnitude t + 2) by omega, pow_add]
      simp only [pow_add]
      field_simp

end

end MeyerGeneralProblem.StrongParity
