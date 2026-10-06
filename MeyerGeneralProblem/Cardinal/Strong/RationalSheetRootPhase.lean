module

public import MeyerGeneralProblem.Cardinal.Strong.RationalSheetPhase
public import MeyerGeneralProblem.Cardinal.Strong.RationalBetaApprox

@[expose] public section

/-! Actual finite rational evaluation of the COMPLETE original integer root equation. -/

namespace MeyerGeneralProblem.StrongParity

/-- The executable original quarter-phase input using the actual parity continuant. -/
def rationalSheetRootInput (x : ℚ) (p : ℕ) : ℚ := rationalBetaApprox p * x - 1 / 4

/-- The raw executable root-equation value at fixed internal precision. -/
def rationalSheetRootPhaseRaw (a x : ℚ) (p : ℕ) : ℚ :=
  x + rationalSheetPhaseApprox a (rationalSheetRootInput x p) p

/-- A definite internal precision paying the actual rational probe magnitude. -/
def rationalSheetRootPrecision (x : ℚ) (p : ℕ) : ℕ := p + rationalMagnitude x + 3

/-- The literal original root equation evaluated by an actual finite rational program. -/
def rationalSheetRootPhaseApprox (a x : ℚ) (p : ℕ) : ℚ :=
  rationalSheetRootPhaseRaw a x (rationalSheetRootPrecision x p)

noncomputable section

/-- The ACTUAL original compact-slot lift amplifies input errors by at most three. -/
theorem sheetPhaseLift_compact_abs_sub_le {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (x y : ℝ) :
    |sheetPhaseLift a x - sheetPhaseLift a y| ≤ 3 * |x - y| := by
  have ha1 : a < 1 := by linarith
  have hbound (z : ℝ) : ‖deriv (sheetPhaseLift a) z‖ ≤ 3 := by
    rw [(sheetPhaseLift_hasDerivAt ha ha1 z).deriv, Real.norm_eq_abs,
      abs_of_pos (sheetLiftSpeed_pos ha ha1 z)]
    exact (sheetLiftSpeed_compact_bounds ha ha2 z).2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := sheetPhaseLift a) (s := Set.univ)
    (C := 3) (fun z _ => (sheetPhaseLift_hasDerivAt ha ha1 z).differentiableAt)
    (fun z _ => hbound z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

/-- Actual error of the COMPUTED original quarter-phase input. -/
theorem rationalSheetRootInput_error (x : ℚ) (p : ℕ) :
    |(rationalSheetRootInput x p : ℝ) - (beta * (x : ℝ) - 1 / 4)| ≤
      |(x : ℝ)| / (2 : ℝ) ^ p := by
  have hi : (rationalSheetRootInput x p : ℝ) - (beta * (x : ℝ) - 1 / 4) =
      ((rationalBetaApprox p : ℝ) - beta) * (x : ℝ) := by
    simp only [rationalSheetRootInput, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat]
    ring
  rw [hi, abs_mul]
  calc
    _ ≤ (1 / (2 : ℝ) ^ p) * |(x : ℝ)| :=
      mul_le_mul_of_nonneg_right (rationalBetaApprox_error p) (abs_nonneg _)
    _ = _ := by ring

/-- Actual original root-equation error before paying the probe magnitude. -/
theorem rationalSheetRootPhaseRaw_error {a : ℚ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (x : ℚ) (p : ℕ) :
    |(rationalSheetRootPhaseRaw a x p : ℝ) - sheetRootPhase a x| ≤
      (1 + 3 * |(x : ℝ)|) / (2 : ℝ) ^ p := by
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha2R : (a : ℝ) ≤ 1 / 2 := by
    have h : (a : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast ha2
    norm_num at h
    exact h
  simp only [rationalSheetRootPhaseRaw, Rat.cast_add, sheetRootPhase, add_sub_add_left_eq_sub]
  calc
    _ ≤ |(rationalSheetPhaseApprox a (rationalSheetRootInput x p) p : ℝ) -
        sheetPhaseLift a (rationalSheetRootInput x p)| +
        |sheetPhaseLift a (rationalSheetRootInput x p) - sheetPhaseLift a (beta * x - 1 / 4)| :=
      abs_sub_le _ _ _
    _ ≤ 1 / (2 : ℝ) ^ p + 3 * (|(x : ℝ)| / (2 : ℝ) ^ p) :=
      add_le_add (rationalSheetPhaseApprox_error ha ha2 _ _)
        ((sheetPhaseLift_compact_abs_sub_le haR ha2R _ _).trans
          (mul_le_mul_of_nonneg_left (rationalSheetRootInput_error x p) (by norm_num)))
    _ = _ := by ring

/-- The actual root-equation evaluator has binary error at EVERY rational probe. -/
theorem rationalSheetRootPhaseApprox_error {a : ℚ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (x : ℚ) (p : ℕ) :
    |(rationalSheetRootPhaseApprox a x p : ℝ) - sheetRootPhase a x| ≤ 1 / (2 : ℝ) ^ p := by
  let M := rationalMagnitude x
  have hM : |(x : ℝ)| ≤ (M : ℝ) := rational_abs_le_magnitude x
  have hb : 1 + 3 * M ≤ 2 ^ (M + 3) := by
    rw [pow_add]
    norm_num
    have h := two_pow_ge_add_one M
    omega
  have hbR : (1 : ℝ) + 3 * M ≤ (2 : ℝ) ^ (M + 3) := by exact_mod_cast hb
  unfold rationalSheetRootPhaseApprox
  calc
    _ ≤ (1 + 3 * |(x : ℝ)|) / (2 : ℝ) ^ rationalSheetRootPrecision x p :=
      rationalSheetRootPhaseRaw_error ha ha2 x _
    _ ≤ (1 + 3 * M) / (2 : ℝ) ^ rationalSheetRootPrecision x p := by gcongr
    _ ≤ (2 : ℝ) ^ (M + 3) / (2 : ℝ) ^ rationalSheetRootPrecision x p := by gcongr
    _ = _ := by
      dsimp [rationalSheetRootPrecision, M]
      rw [show p + rationalMagnitude x + 3 = p + (rationalMagnitude x + 3) by omega]
      simp only [pow_add]
      field_simp

end

end MeyerGeneralProblem.StrongParity
