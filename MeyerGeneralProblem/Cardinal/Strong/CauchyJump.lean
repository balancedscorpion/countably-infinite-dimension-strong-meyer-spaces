module

public import MeyerGeneralProblem.Cardinal.Strong.CauchyPeak

@[expose] public section

/-! The actual integrated jump of a simple real pole, including its sign
and normalization. No distributional boundary identity is assumed. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- The literal upper-minus-lower values of one real principal part. -/
def realPoleJump (res : ℂ) (a t x : ℝ) : ℂ :=
  res / ((x - a : ℝ) + t * Complex.I) - res / ((x - a : ℝ) - t * Complex.I)

theorem cauchyPeakProfile_scaled {t : ℝ} (ht : t ≠ 0) (a x : ℝ) :
    t⁻¹ * cauchyPeakProfile (t⁻¹ * (a - x)) =
      Real.pi⁻¹ * t / ((x - a) ^ 2 + t ^ 2) := by
  have hd : (x - a) ^ 2 + t ^ 2 ≠ 0 := by
    have hp := sq_pos_of_ne_zero ht
    nlinarith [sq_nonneg (x - a)]
  unfold cauchyPeakProfile
  field_simp
  ring

/-- Exact kernel identity with the original negative Fourier jump convention. -/
theorem realPoleJump_eq_cauchy {t : ℝ} (ht : t ≠ 0) (res : ℂ) (a x : ℝ) :
    realPoleJump res a t x =
      -((2 * Real.pi : ℝ) * Complex.I) * res *
        (t⁻¹ * cauchyPeakProfile (t⁻¹ * (a - x)) : ℝ) := by
  have hu : ((x - a : ℝ) + t * Complex.I : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, zero_mul, mul_one, zero_add, Complex.zero_im] at hi
    exact ht (by simpa only [add_zero] using hi)
  have hl : ((x - a : ℝ) - t * Complex.I : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, zero_mul, mul_one, Complex.zero_im] at hi
    exact ht (by linarith)
  have hd : (x - a) ^ 2 + t ^ 2 ≠ 0 := by
    have hp := sq_pos_of_ne_zero ht
    nlinarith [sq_nonneg (x - a)]
  rw [cauchyPeakProfile_scaled ht]
  unfold realPoleJump
  have hu' : ((x : ℂ) - a + t * Complex.I) ≠ 0 := by
    simpa only [Complex.ofReal_sub] using hu
  have hl' : ((x : ℂ) - a - t * Complex.I) ≠ 0 := by
    simpa only [Complex.ofReal_sub] using hl
  have hd' : (((x : ℂ) - a) ^ 2 + (t : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast hd
  push_cast
  field_simp [hu', hl', hd', Real.pi_ne_zero]
  ring_nf
  norm_num [pow_succ, Complex.I_sq]
  ring

/-- Integrating the actual pole jump yields the actual mass against every integrable test
continuous at the pole. -/
theorem realPoleJump_integral_tendsto (res : ℂ) {a : ℝ} {g : ℝ → ℂ}
    (hg : Integrable g) (hga : ContinuousAt g a) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, realPoleJump res a t x * g x)
      (𝓝[>] 0) (𝓝 (-((2 * Real.pi : ℝ) * Complex.I) * res * g a)) := by
  have h := ((cauchyPeak_integral_tendsto hg hga).comp
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))).const_mul
      (-((2 * Real.pi : ℝ) * Complex.I) * res)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change -((2 * Real.pi : ℝ) * Complex.I) * res *
    (∫ x : ℝ, (t⁻¹ * cauchyPeakProfile (t⁻¹ * (a - x))) • g x) = _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [realPoleJump_eq_cauchy (ne_of_gt ht)]
  simp only [Complex.real_smul]
  ring

theorem cauchyPeakProfile_continuous : Continuous cauchyPeakProfile := by
  unfold cauchyPeakProfile
  have hc : Continuous (fun x : ℝ => 1 + x ^ 2) := continuous_const.add (continuous_id.pow 2)
  exact continuous_const.mul (hc.inv₀ (fun x : ℝ => by nlinarith [sq_nonneg x]))

theorem cauchyPeakProfile_le (x : ℝ) : cauchyPeakProfile x ≤ Real.pi⁻¹ := by
  unfold cauchyPeakProfile
  apply mul_le_of_le_one_right (inv_nonneg.mpr Real.pi_pos.le)
  rw [inv_eq_one_div]
  convert! one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
    (show (1 : ℝ) ≤ 1 + x ^ 2 by nlinarith [sq_nonneg x]) using 1
  norm_num

/-- The original pole jump is integrable against every integrable test at every
strictly positive tube height. -/
theorem realPoleJump_mul_integrable (res : ℂ) (a : ℝ) {t : ℝ} (ht : 0 < t)
    {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun x : ℝ => realPoleJump res a t x * g x) := by
  have hc : Continuous (realPoleJump res a t) := by
    have heq : realPoleJump res a t = fun x : ℝ =>
        -((2 * Real.pi : ℝ) * Complex.I) * res *
          (t⁻¹ * cauchyPeakProfile (t⁻¹ * (a - x)) : ℝ) := by
      funext x
      exact realPoleJump_eq_cauchy (ne_of_gt ht) res a x
    rw [heq]
    have hp := cauchyPeakProfile_continuous
    fun_prop
  apply hg.bdd_mul (c := ‖-((2 * Real.pi : ℝ) * Complex.I) * res‖ * (t⁻¹ * Real.pi⁻¹))
    hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [realPoleJump_eq_cauchy (ne_of_gt ht), norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (inv_pos.mpr ht).le (cauchyPeakProfile_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (cauchyPeakProfile_le _) (inv_pos.mpr ht).le) (norm_nonneg _)

end

end MeyerGeneralProblem.StrongParity
