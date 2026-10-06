module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginalZCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.BidiskSeries

@[expose] public section

/-! Complete actual compact original reciprocal Taylor coefficients and uniform bounds. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The actual Taylor coefficient, defined by the derivative at zero. -/
def compactOriginalUpperCoefficient {s : ℕ} (block : CompactOriginalParameterBlock s) (k n : ℕ) : ℂ :=
  iteratedDeriv n (compactOriginalZCoefficient block k) 0 / (n.factorial : ℂ)

/-- Every actual Taylor coefficient has the original polynomial growth bound. -/
theorem compactOriginalUpperCoefficient_norm_le {s : ℕ} (block : CompactOriginalParameterBlock s) (k n : ℕ) :
    ‖compactOriginalUpperCoefficient block k n‖ ≤ (k + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block := by
  have hf : DiffContOnCl ℂ (compactOriginalZCoefficient block k) (Metric.ball 0 1) :=
    ((compactOriginalZCoefficient_differentiableOn block k).mono
      Metric.closure_ball_subset_closedBall).diffContOnCl
  have hb : ∀ W ∈ Metric.sphere (0 : ℂ) 1,
      ‖compactOriginalZCoefficient block k W‖ ≤ (k + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block := by
    intro W hW
    exact compactOriginalZCoefficient_norm_le block k
      (by simpa only [Metric.mem_sphere, dist_zero_right] using (le_of_eq hW))
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1) hf hb
  simp only [one_pow, div_one] at h
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold compactOriginalUpperCoefficient
  rw [norm_div, norm_natCast]
  exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using h)

/-- The actual W Taylor series represents the literal finite Z coefficient. -/
theorem compactOriginalUpperCoefficient_hasSum {s : ℕ} (block : CompactOriginalParameterBlock s) (k : ℕ) {W : ℂ} (hW : ‖W‖ < 1) :
    HasSum (fun n : ℕ => compactOriginalUpperCoefficient block k n * W ^ n)
      (compactOriginalZCoefficient block k W) := by
  have hf := (compactOriginalZCoefficient_differentiableOn block k).mono Metric.ball_subset_closedBall
  have hWball : W ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hW
  have hs := Complex.hasSum_taylorSeries_on_ball hf hWball
  simpa only [compactOriginalUpperCoefficient, sub_zero, smul_eq_mul, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hs

/-- The actual two-index reciprocal series is absolutely summable on the open bidisk. -/
theorem compactOriginalUpperCoefficient_bidisk_summable {s : ℕ} (block : CompactOriginalParameterBlock s) {Z W : ℂ}
    (hZ : ‖Z‖ < 1) (hW : ‖W‖ < 1) :
    Summable (fun p : ℕ × ℕ => compactOriginalUpperCoefficient block p.1 p.2 * Z ^ p.1 * W ^ p.2) := by
  let ρ := (1 + ‖Z‖) / 2
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hZρ : ‖Z‖ ≤ ρ := by dsimp [ρ]; linarith
  have hC := compactOriginalPolydiskConstant_pos block
  have hrow : Summable (fun k : ℕ =>
      (k + 1 : ℝ) ^ s * ρ ^ k / compactOriginalPolydiskConstant block) :=
    (summable_shiftedPower_geometric s hρ0 hρ1).div_const _
  have hcol : Summable (fun n : ℕ => ‖W‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg _) hW
  have hmajor := hrow.mul_of_nonneg hcol
    (fun k => by positivity) (fun n => pow_nonneg (norm_nonneg W) n)
  apply Summable.of_norm_bounded hmajor
  intro p
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  have hpow : ‖Z‖ ^ p.1 ≤ ρ ^ p.1 := pow_le_pow_left₀ (norm_nonneg Z) hZρ _
  have hmul : ‖compactOriginalUpperCoefficient block p.1 p.2‖ * ‖Z‖ ^ p.1 ≤
      ((p.1 + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block) * ρ ^ p.1 :=
    mul_le_mul (compactOriginalUpperCoefficient_norm_le block p.1 p.2) hpow
      (pow_nonneg (norm_nonneg Z) _) (by positivity)
  exact (mul_le_mul_of_nonneg_right hmul (pow_nonneg (norm_nonneg W) _)).trans_eq (by ring)

/-- The complete actual two-index series equals the original product reciprocal. -/
theorem compactOriginalUpperCoefficient_bidisk_hasSum {s : ℕ} (block : CompactOriginalParameterBlock s) {Z W : ℂ}
    (hZ : ‖Z‖ < 1) (hW : ‖W‖ < 1) :
    HasSum (fun p : ℕ × ℕ => compactOriginalUpperCoefficient block p.1 p.2 * Z ^ p.1 * W ^ p.2)
      (compactOriginalSheetPolynomial block Z W)⁻¹ := by
  have hs := compactOriginalUpperCoefficient_bidisk_summable block hZ hW
  have hrow (k : ℕ) :
      HasSum (fun n : ℕ => compactOriginalUpperCoefficient block k n * Z ^ k * W ^ n)
        (compactOriginalZCoefficient block k W * Z ^ k) := by
    convert! (compactOriginalUpperCoefficient_hasSum block k hW).mul_right (Z ^ k) using 1
    funext n
    ring
  have hg := hs.hasSum.prod_fiberwise hrow
  have hZsum := compactOriginalZCoefficient_hasSum block hZ hW.le
  rw [← hg.unique hZsum]
  exact hs.hasSum

/-- EVERY complete compact original reciprocal coefficient has a definite integer growth bound. -/
theorem compactOriginalUpperCoefficient_uniform_norm_le {s : ℕ}
    (block : CompactOriginalParameterBlock s) (k n : ℕ) :
    ‖compactOriginalUpperCoefficient block k n‖ ≤ (2 : ℝ) ^ s * (k + 1 : ℝ) ^ s := by
  calc
    _ ≤ (k + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block :=
      compactOriginalUpperCoefficient_norm_le block k n
    _ = (1 / compactOriginalPolydiskConstant block) * (k + 1 : ℝ) ^ s := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (compactOriginalPolydiskConstant_inv_le block) (by positivity)

/-- The actual compact reciprocal constant coefficient is exactly one. -/
theorem compactOriginalUpperCoefficient_zero_zero {s : ℕ} (block : CompactOriginalParameterBlock s) :
    compactOriginalUpperCoefficient block 0 0 = 1 := by
  have hs := compactOriginalUpperCoefficient_bidisk_hasSum block
    (Z := 0) (W := 0) (by norm_num) (by norm_num)
  have hsingle : HasSum (fun p : ℕ × ℕ =>
      compactOriginalUpperCoefficient block p.1 p.2 * (0 : ℂ) ^ p.1 * (0 : ℂ) ^ p.2)
      (compactOriginalUpperCoefficient block 0 0) := by
    convert! hasSum_single (f := fun p : ℕ × ℕ =>
      compactOriginalUpperCoefficient block p.1 p.2 * (0 : ℂ) ^ p.1 * (0 : ℂ) ^ p.2)
      (0, 0) (fun p hp => ?_) using 1
    · simp only [pow_zero, mul_one]
    · by_cases hk : p.1 = 0
      · have hn : p.2 ≠ 0 := fun hn => hp (Prod.ext hk hn)
        simp only [zero_pow hn, mul_zero]
      · simp only [zero_pow hk, mul_zero, zero_mul]
  simpa only [compactOriginalSheetPolynomial_zero_zero, inv_one] using hsingle.unique hs

end

end MeyerGeneralProblem.StrongParity
