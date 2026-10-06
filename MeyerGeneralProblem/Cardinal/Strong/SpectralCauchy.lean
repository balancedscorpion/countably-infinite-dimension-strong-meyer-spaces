module

public import MeyerGeneralProblem.Cardinal.Strong.ProductZCoefficients
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries

@[expose] public section

/-! Cauchy estimates for the actual W Taylor coefficients of the literal
finite product Z coefficients. Their holomorphy and boundary bounds are
proved on the original closed unit disk. No Fourier identity is presumed. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The actual Taylor coefficient, defined by the derivative at zero. -/
def productUpperCoefficient (s k n : ℕ) : ℂ :=
  iteratedDeriv n (productZCoefficient s k) 0 / (n.factorial : ℂ)

/-- Every actual Taylor coefficient has the original polynomial growth bound. -/
theorem productUpperCoefficient_norm_le (s k n : ℕ) :
    ‖productUpperCoefficient s k n‖ ≤ (k + 1 : ℝ) ^ s / productPolydiskConstant s := by
  have hf : DiffContOnCl ℂ (productZCoefficient s k) (Metric.ball 0 1) :=
    ((productZCoefficient_differentiableOn s k).mono
      Metric.closure_ball_subset_closedBall).diffContOnCl
  have hb : ∀ W ∈ Metric.sphere (0 : ℂ) 1,
      ‖productZCoefficient s k W‖ ≤ (k + 1 : ℝ) ^ s / productPolydiskConstant s := by
    intro W hW
    exact productZCoefficient_norm_le s k
      (by simpa only [Metric.mem_sphere, dist_zero_right] using (le_of_eq hW))
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1) hf hb
  simp only [one_pow, div_one] at h
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold productUpperCoefficient
  rw [norm_div, norm_natCast]
  exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using h)

/-- The actual W Taylor series represents the literal finite Z coefficient. -/
theorem productUpperCoefficient_hasSum (s k : ℕ) {W : ℂ} (hW : ‖W‖ < 1) :
    HasSum (fun n : ℕ => productUpperCoefficient s k n * W ^ n)
      (productZCoefficient s k W) := by
  have hf := (productZCoefficient_differentiableOn s k).mono Metric.ball_subset_closedBall
  have hWball : W ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hW
  have hs := Complex.hasSum_taylorSeries_on_ball hf hWball
  simpa only [productUpperCoefficient, sub_zero, smul_eq_mul, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hs

end

end MeyerGeneralProblem.StrongParity
