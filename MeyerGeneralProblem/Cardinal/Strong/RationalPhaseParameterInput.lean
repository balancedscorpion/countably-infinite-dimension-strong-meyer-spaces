module

public import MeyerGeneralProblem.Cardinal.Strong.RationalSheetRootPhase

@[expose] public section

/-! Actual parameter/probe perturbation for the literal computed original root equation.
The final parameter names must still be constructed; these bounds expose
exactly the input errors consumed by the already implemented finite program.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The ACTUAL original tangent is uniformly stable under compact parameter changes. -/
theorem sheetLiftTangent_parameter_abs_sub_le {a b : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hb : 0 ≤ b) (hb2 : b ≤ 1 / 2) (t : ℝ) :
    |sheetLiftTangent a t - sheetLiftTangent b t| ≤ 4 * |a - b| := by
  have hDa := sheetLiftDenominator_compact_lower ha ha2 t
  have hDb := sheetLiftDenominator_compact_lower hb hb2 t
  have hDap : 0 < sheetLiftDenominator a t := by linarith
  have hDbp : 0 < sheetLiftDenominator b t := by linarith
  have hDp : 0 < sheetLiftDenominator a t * sheetLiftDenominator b t := mul_pos hDap hDbp
  have hD : 1 / 4 ≤ sheetLiftDenominator a t * sheetLiftDenominator b t := by
    have h := mul_le_mul hDa hDb (by norm_num : (0 : ℝ) ≤ 1 / 2) hDap.le
    norm_num at h
    exact h
  have hi : sheetLiftTangent a t - sheetLiftTangent b t =
      (a - b) * Real.sin (2 * Real.pi * t) /
        (sheetLiftDenominator a t * sheetLiftDenominator b t) := by
    unfold sheetLiftTangent
    field_simp
    dsimp [sheetLiftDenominator]
    ring
  rw [hi, abs_div, abs_mul, abs_of_pos hDp]
  calc
    _ ≤ |a - b| / (sheetLiftDenominator a t * sheetLiftDenominator b t) := by
      apply div_le_div_of_nonneg_right _ hDp.le
      simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg (a - b))
    _ ≤ 4 * |a - b| := (div_le_iff₀ hDp).mpr (by nlinarith [abs_nonneg (a - b)])

/-- The ACTUAL original lift has a uniform compact parameter-error bound. -/
theorem sheetPhaseLift_parameter_abs_sub_le {a b : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hb : 0 ≤ b) (hb2 : b ≤ 1 / 2) (t : ℝ) :
    |sheetPhaseLift a t - sheetPhaseLift b t| ≤ 2 * |a - b| := by
  have hi : sheetPhaseLift a t - sheetPhaseLift b t =
      (Real.arctan (sheetLiftTangent a t) - Real.arctan (sheetLiftTangent b t)) / Real.pi := by
    dsimp [sheetPhaseLift]
    ring
  rw [hi, abs_div, abs_of_pos Real.pi_pos]
  calc
    _ ≤ |sheetLiftTangent a t - sheetLiftTangent b t| / Real.pi :=
      div_le_div_of_nonneg_right (arctan_abs_sub_le _ _) Real.pi_pos.le
    _ ≤ 4 * |a - b| / Real.pi :=
      div_le_div_of_nonneg_right (sheetLiftTangent_parameter_abs_sub_le ha ha2 hb hb2 t)
        Real.pi_pos.le
    _ ≤ 2 * |a - b| := (div_le_iff₀ Real.pi_pos).mpr (by nlinarith [Real.pi_gt_three, abs_nonneg (a - b)])

/-- The ENTIRE original root equation keeps the same compact parameter-error bound. -/
theorem sheetRootPhase_parameter_abs_sub_le {a b : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hb : 0 ≤ b) (hb2 : b ≤ 1 / 2) (x : ℝ) :
    |sheetRootPhase a x - sheetRootPhase b x| ≤ 2 * |a - b| := by
  simpa only [sheetRootPhase, add_sub_add_left_eq_sub] using
    sheetPhaseLift_parameter_abs_sub_le ha ha2 hb hb2 (beta * x - 1 / 4)

/-- The ACTUAL original equation amplifies probe error by at most thirteen. -/
theorem sheetRootPhase_compact_abs_sub_le {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (x y : ℝ) :
    |sheetRootPhase a x - sheetRootPhase a y| ≤ 13 * |x - y| := by
  have ha1 : a < 1 := by linarith
  have hbound (z : ℝ) : ‖deriv (sheetRootPhase a) z‖ ≤ 13 := by
    have h := sheetRootPhase_compact_deriv_bounds ha ha2 z
    rw [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < deriv (sheetRootPhase a) z)]
    exact h.2.le
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := sheetRootPhase a) (s := Set.univ)
    (C := 13) (fun z _ => (sheetRootPhase_hasDerivAt ha ha1 z).differentiableAt)
    (fun z _ => hbound z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

/-- Actual computed root-equation error for an approximated REAL parameter. -/
theorem rationalSheetRootPhaseApprox_real_parameter_error {q : ℚ}
    (hq : 0 ≤ q) (hq2 : q ≤ 1 / 2) {a epsilon : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (he : |(q : ℝ) - a| ≤ epsilon) (x : ℚ) (p : ℕ) :
    |(rationalSheetRootPhaseApprox q x p : ℝ) - sheetRootPhase a x| ≤
      1 / (2 : ℝ) ^ p + 2 * epsilon := by
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq2R : (q : ℝ) ≤ 1 / 2 := by
    have h : (q : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hq2
    norm_num at h
    exact h
  calc
    _ ≤ |(rationalSheetRootPhaseApprox q x p : ℝ) - sheetRootPhase q x| +
        |sheetRootPhase q x - sheetRootPhase a x| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (rationalSheetRootPhaseApprox_error hq hq2 x p)
      ((sheetRootPhase_parameter_abs_sub_le hqR hq2R ha ha2 x).trans
        (mul_le_mul_of_nonneg_left he (by norm_num)))

/-- Actual computed error when BOTH the real parameter and real probe are approximated. -/
theorem rationalSheetRootPhaseApprox_real_input_error {q : ℚ}
    (hq : 0 ≤ q) (hq2 : q ≤ 1 / 2) {a epsilon_a z epsilon_x : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (he_a : |(q : ℝ) - a| ≤ epsilon_a)
    (x : ℚ) (he_x : |(x : ℝ) - z| ≤ epsilon_x) (p : ℕ) :
    |(rationalSheetRootPhaseApprox q x p : ℝ) - sheetRootPhase a z| ≤
      1 / (2 : ℝ) ^ p + 2 * epsilon_a + 13 * epsilon_x := by
  calc
    _ ≤ |(rationalSheetRootPhaseApprox q x p : ℝ) - sheetRootPhase a x| +
        |sheetRootPhase a x - sheetRootPhase a z| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (rationalSheetRootPhaseApprox_real_parameter_error hq hq2 ha ha2 he_a x p)
      ((sheetRootPhase_compact_abs_sub_le ha ha2 x z).trans
        (mul_le_mul_of_nonneg_left he_x (by norm_num)))

end

end MeyerGeneralProblem.StrongParity
