module

public import MeyerGeneralProblem.Cardinal.Strong.ProductPowerSeries
public import MeyerGeneralProblem.Cardinal.Strong.SpectralCauchy

@[expose] public section

/-! Absolute convergence and exact evaluation of the literal reciprocal
bidisk series. Both indices and the original denominator are retained. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem summable_shiftedPower_geometric (s : ℕ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun k : ℕ => (k + 1 : ℝ) ^ s * r ^ k) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hr0] using hr1
  have hs := (summable_pow_mul_geometric_of_norm_lt_one s hr).comp_injective Nat.succ_injective
  have hd := hs.div_const r
  convert! hd using 1
  funext k
  simp only [Function.comp_def, Nat.cast_succ]
  rw [pow_succ, ← mul_assoc, mul_div_cancel_right₀ _ (ne_of_gt hr0)]

/-- The actual two-index reciprocal series is absolutely summable on the open bidisk. -/
theorem productUpperCoefficient_bidisk_summable (s : ℕ) {Z W : ℂ}
    (hZ : ‖Z‖ < 1) (hW : ‖W‖ < 1) :
    Summable (fun p : ℕ × ℕ => productUpperCoefficient s p.1 p.2 * Z ^ p.1 * W ^ p.2) := by
  let ρ := (1 + ‖Z‖) / 2
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hZρ : ‖Z‖ ≤ ρ := by dsimp [ρ]; linarith
  have hC := productPolydiskConstant_pos s
  have hrow : Summable (fun k : ℕ =>
      (k + 1 : ℝ) ^ s * ρ ^ k / productPolydiskConstant s) :=
    (summable_shiftedPower_geometric s hρ0 hρ1).div_const _
  have hcol : Summable (fun n : ℕ => ‖W‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg _) hW
  have hmajor := hrow.mul_of_nonneg hcol
    (fun k => by positivity) (fun n => pow_nonneg (norm_nonneg W) n)
  apply Summable.of_norm_bounded hmajor
  intro p
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  have hpow : ‖Z‖ ^ p.1 ≤ ρ ^ p.1 := pow_le_pow_left₀ (norm_nonneg Z) hZρ _
  have hmul : ‖productUpperCoefficient s p.1 p.2‖ * ‖Z‖ ^ p.1 ≤
      ((p.1 + 1 : ℝ) ^ s / productPolydiskConstant s) * ρ ^ p.1 :=
    mul_le_mul (productUpperCoefficient_norm_le s p.1 p.2) hpow
      (pow_nonneg (norm_nonneg Z) _) (by positivity)
  exact (mul_le_mul_of_nonneg_right hmul (pow_nonneg (norm_nonneg W) _)).trans_eq (by ring)

/-- The complete actual two-index series equals the original product reciprocal. -/
theorem productUpperCoefficient_bidisk_hasSum (s : ℕ) {Z W : ℂ}
    (hZ : ‖Z‖ < 1) (hW : ‖W‖ < 1) :
    HasSum (fun p : ℕ × ℕ => productUpperCoefficient s p.1 p.2 * Z ^ p.1 * W ^ p.2)
      (productSheetPolynomial s Z W)⁻¹ := by
  have hs := productUpperCoefficient_bidisk_summable s hZ hW
  have hrow (k : ℕ) :
      HasSum (fun n : ℕ => productUpperCoefficient s k n * Z ^ k * W ^ n)
        (productZCoefficient s k W * Z ^ k) := by
    convert! (productUpperCoefficient_hasSum s k hW).mul_right (Z ^ k) using 1
    funext n
    ring
  have hg := hs.hasSum.prod_fiberwise hrow
  have hZsum := productZCoefficient_hasSum s hZ hW.le
  rw [← hg.unique hZsum]
  exact hs.hasSum

end

end MeyerGeneralProblem.StrongParity
