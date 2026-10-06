module

public import MeyerGeneralProblem.Cardinal.Strong.SheetPhaseLift

@[expose] public section

/-! Derivative and quantitative monotonicity of the explicit ORIGINAL phase lift. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- An explicit real formula for the original Blaschke circle speed. -/
def sheetLiftSpeed (a t : ℝ) : ℝ :=
  (1 - a ^ 2) / (1 - 2 * a * Real.cos (2 * Real.pi * t) + a ^ 2)

theorem unitPhase_sub_normSq (a t : ℝ) :
    Complex.normSq (unitPhase t - a) = 1 - 2 * a * Real.cos (2 * Real.pi * t) + a ^ 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, unitPhase, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * t)]

theorem sheetLiftSpeed_eq_circleSpeed (a t : ℝ) :
    sheetLiftSpeed a t = sheetCircleSpeed a (unitPhase t) := by
  rw [sheetLiftSpeed, sheetCircleSpeed, unitPhase_sub_normSq]

theorem sheetLiftSpeed_pos {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    0 < sheetLiftSpeed a t := by
  rw [sheetLiftSpeed_eq_circleSpeed]
  exact sheetCircleSpeed_pos ha ha1 (unitPhase_norm t)

theorem sheetLiftTangent_hasDerivAt {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    HasDerivAt (sheetLiftTangent a)
      (2 * Real.pi * a * (Real.cos (2 * Real.pi * t) - a) /
        sheetLiftDenominator a t ^ 2) t := by
  have hθ : HasDerivAt (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
  have hnum := hθ.sin.const_mul a
  have hden := (hasDerivAt_const t (1 : ℝ)).sub (hθ.cos.const_mul a)
  have hd := (sheetLiftDenominator_pos ha ha1 t).ne'
  have h := hnum.div hden hd
  convert! h using 1
  dsimp [sheetLiftDenominator]
  congr 1
  linear_combination 2 * Real.pi * a ^ 2 * Real.sin_sq_add_cos_sq (2 * Real.pi * t)

/-- The explicit real lift has exactly the original positive circle derivative. -/
theorem sheetPhaseLift_hasDerivAt {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    HasDerivAt (sheetPhaseLift a) (sheetLiftSpeed a t) t := by
  have hd := (sheetLiftDenominator_pos ha ha1 t).ne'
  have hD : 1 - 2 * a * Real.cos (2 * Real.pi * t) + a ^ 2 ≠ 0 := by
    rw [← unitPhase_sub_normSq]
    exact (Complex.normSq_pos.mpr
      (unitCircle_sub_parameter_ne_zero ha ha1 (unitPhase_norm t))).ne'
  have hsum : sheetLiftDenominator a t ^ 2 + (a * Real.sin (2 * Real.pi * t)) ^ 2 =
      1 - 2 * a * Real.cos (2 * Real.pi * t) + a ^ 2 := by
    dsimp [sheetLiftDenominator]
    linear_combination a ^ 2 * Real.sin_sq_add_cos_sq (2 * Real.pi * t)
  have hq : 1 + sheetLiftTangent a t ^ 2 =
      (1 - 2 * a * Real.cos (2 * Real.pi * t) + a ^ 2) /
        sheetLiftDenominator a t ^ 2 := by
    dsimp [sheetLiftTangent]
    rw [div_pow, one_add_div (pow_ne_zero 2 hd), hsum]
  have h := (hasDerivAt_id t).add
    ((sheetLiftTangent_hasDerivAt ha ha1 t).arctan.div_const Real.pi)
  convert! h using 1
  rw [hq]
  dsimp [sheetLiftSpeed]
  ring_nf at hD ⊢
  field_simp [hd, hD]
  linear_combination (mul_inv_cancel₀ hD)

theorem sheetPhaseLift_strictMono {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    StrictMono (sheetPhaseLift a) :=
  strictMono_of_hasDerivAt_pos (sheetPhaseLift_hasDerivAt ha ha1)
    (sheetLiftSpeed_pos ha ha1)

theorem sheetPhaseLift_continuous {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Continuous (sheetPhaseLift a) :=
  continuous_iff_continuousAt.mpr fun t => (sheetPhaseLift_hasDerivAt ha ha1 t).continuousAt

end

end MeyerGeneralProblem.StrongParity
