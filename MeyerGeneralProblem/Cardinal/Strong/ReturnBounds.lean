module

public import MeyerGeneralProblem.Cardinal.Strong.PrivateReturnSequence

@[expose] public section

/-! Quantitative approach to the original corner along actual sheet
returns, and the original torus derivative upper bound. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem quarterReturn_phase_bounds (n m : ℤ) (x : ℝ)
    (hnear : |x - (n : ℝ)| ≤ |beta * n - m - 1 / 4|) :
    ‖unitPhase x - 1‖ ≤ 2 * Real.pi * |beta * n - m - 1 / 4| ∧
    ‖unitPhase (beta * x - 1 / 4) - 1‖ ≤
      2 * Real.pi * (1 + beta) * |beta * n - m - 1 / 4| ∧
    ‖unitPhase x - unitPhase (beta * x - 1 / 4)‖ ≤
      2 * Real.pi * beta * |beta * n - m - 1 / 4| := by
  have hb : 0 < beta := by linarith [beta_between_three_four.1]
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hz := unitPhase_norm_sub_upper x (n : ℝ)
  rw [unitPhase_integer] at hz
  have hw := unitPhase_norm_sub_upper (beta * x - 1 / 4) (m : ℝ)
  rw [unitPhase_integer] at hw
  have hwerror : |beta * x - 1 / 4 - m| ≤ (1 + beta) * |beta * n - m - 1 / 4| := by
    calc
      _ = |beta * (x - n) + (beta * n - m - 1 / 4)| := by congr 1; ring
      _ ≤ |beta * (x - n)| + |beta * n - m - 1 / 4| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_pos hb]
        nlinarith [mul_le_mul_of_nonneg_left hnear hb.le]
  refine ⟨hz.trans (mul_le_mul_of_nonneg_left hnear hπ), ?_, ?_⟩
  · exact hw.trans ((mul_le_mul_of_nonneg_left hwerror hπ).trans_eq (by ring))
  · rw [← unitPhase_sub_integer x n, ← unitPhase_sub_integer (beta * x - 1 / 4) m]
    apply (unitPhase_norm_sub_upper _ _).trans
    have hqerror : |(x - n) - (beta * x - 1 / 4 - m)| ≤
        beta * |beta * n - m - 1 / 4| := by
      calc
        _ = |(1 - beta) * (x - n) - (beta * n - m - 1 / 4)| := by congr 1; ring
        _ ≤ |(1 - beta) * (x - n)| + |beta * n - m - 1 / 4| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_mul, abs_of_nonpos (by linarith [beta_between_three_four.1] : 1 - beta ≤ 0)]
          nlinarith [mul_le_mul_of_nonneg_left hnear
            (by linarith [beta_between_three_four.1] : 0 ≤ beta - 1)]
    exact (mul_le_mul_of_nonneg_left hqerror hπ).trans_eq (by ring)

theorem privateSheetRoot_phase_bounds (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ‖unitPhase (privateSheetRoot a ha n) - 1‖ ≤ 2 * Real.pi * |privateReturnError n| ∧
    ‖unitPhase (beta * privateSheetRoot a ha n - 1 / 4) - 1‖ ≤
      2 * Real.pi * (1 + beta) * |privateReturnError n| ∧
    ‖unitPhase (privateSheetRoot a ha n) - unitPhase (beta * privateSheetRoot a ha n - 1 / 4)‖ ≤
      2 * Real.pi * beta * |privateReturnError n| :=
  quarterReturn_phase_bounds _ _ _ (privateSheetRoot_distance a ha n)

/-- The actual original sheet torus derivative has a uniform upper bound. -/
theorem sheetTorusDerivative_norm_upper {a : ℝ} (ha : 0 ≤ a) {Z W : ℂ}
    (hZ : ‖Z‖ = 1) (hW : ‖W‖ = 1) :
    ‖sheetTorusDerivative a Z W‖ ≤ (1 + beta) * (1 + a) := by
  have hb : 0 < beta := by linarith [beta_between_three_four.1]
  have hu : ‖(a : ℂ) * Z - Z * W‖ ≤ a + 1 := by
    simpa only [norm_mul, hZ, hW, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ha, mul_one, one_mul] using norm_sub_le ((a : ℂ) * Z) (Z * W)
  have hv : ‖-(a : ℂ) * W - Z * W‖ ≤ a + 1 := by
    simpa only [norm_mul, norm_neg, hZ, hW, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ha, mul_one, one_mul] using norm_sub_le (-(a : ℂ) * W) (Z * W)
  unfold sheetTorusDerivative
  calc
    _ ≤ ‖(a : ℂ) * Z - Z * W‖ + ‖(beta : ℂ) * (-(a : ℂ) * W - Z * W)‖ := norm_add_le _ _
    _ = ‖(a : ℂ) * Z - Z * W‖ + beta * ‖-(a : ℂ) * W - Z * W‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hv hb.le]

end

end MeyerGeneralProblem.StrongParity
