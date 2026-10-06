module

public import MeyerGeneralProblem.Cardinal.Strong.DampedFourierIntegral

@[expose] public section

/-! The integrated jump of a measurable remainder continuous on an actual
compact neighborhood vanishes on tests supported in its interior. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open Filter MeasureTheory
open scoped Topology

theorem real_vertical_dist_le (x a t : ℝ) :
    dist ((x : ℂ) + (t : ℂ) * Complex.I) (a : ℂ) ≤ |x - a| + |t| := by
  rw [dist_eq_norm, show (x : ℂ) + (t : ℂ) * Complex.I - a =
    ((x - a : ℝ) : ℂ) + (t : ℂ) * Complex.I by push_cast; ring]
  convert! norm_add_le ((x - a : ℝ) : ℂ) ((t : ℂ) * Complex.I) using 1
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]

theorem continuousRemainder_jump_mul_integrable (H : ℂ → ℂ) (a : ℝ) {δ t : ℝ}
    (hHm : Measurable H) (hH : ContinuousOn H (Metric.closedBall (a : ℂ) (2 * δ)))
    (ht : 0 < t ∧ t < δ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, f x ≠ 0 → |x - a| ≤ δ) :
    Integrable (fun x : ℝ =>
      (H ((x : ℂ) + (t : ℂ) * Complex.I) - H ((x : ℂ) - (t : ℂ) * Complex.I)) * f x) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (a : ℂ) (2 * δ)).exists_bound_of_continuousOn hH
  have hp : Continuous (fun x : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hn : Continuous (fun x : ℝ => (x : ℂ) - (t : ℂ) * Complex.I) := by fun_prop
  apply (f.integrable.norm.const_mul (2 * C)).mono'
    (((hHm.comp hp.measurable).sub (hHm.comp hn.measurable)).mul
      f.continuous.measurable).aestronglyMeasurable
  filter_upwards [] with x
  change ‖(H ((x : ℂ) + (t : ℂ) * Complex.I) -
    H ((x : ℂ) - (t : ℂ) * Complex.I)) * f x‖ ≤ (2 * C) * ‖f x‖
  by_cases hx : f x = 0
  · simp only [hx, mul_zero, norm_zero, le_refl]
  · have hball (u : ℝ) (hu : |u| ≤ δ) :
        (x : ℂ) + (u : ℂ) * Complex.I ∈ Metric.closedBall (a : ℂ) (2 * δ) :=
      Metric.mem_closedBall.mpr ((real_vertical_dist_le x a u).trans (by linarith [hf x hx]))
    have hp' := hC _ (hball t (by rw [abs_of_pos ht.1]; exact ht.2.le))
    have hn' := hC _ (hball (-t) (by rw [abs_neg, abs_of_pos ht.1]; exact ht.2.le))
    have hb : ‖H ((x : ℂ) + (t : ℂ) * Complex.I) -
        H ((x : ℂ) - (t : ℂ) * Complex.I)‖ ≤ 2 * C := by
      rw [show (x : ℂ) - (t : ℂ) * Complex.I =
        (x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact (norm_sub_le _ _).trans (by linarith)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- A literal continuous remainder contributes zero after integration. The bound
comes from compactness and is multiplied by the integrable original test norm. -/
theorem continuousRemainder_jump_integral_tendsto (H : ℂ → ℂ) (a : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hHm : Measurable H)
    (hH : ContinuousOn H (Metric.closedBall (a : ℂ) (2 * δ)))
    (f : SchwartzMap ℝ ℂ) (hf : ∀ x : ℝ, f x ≠ 0 → |x - a| ≤ δ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ,
      (H ((x : ℂ) + (t : ℂ) * Complex.I) - H ((x : ℂ) - (t : ℂ) * Complex.I)) * f x)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (a : ℂ) (2 * δ)).exists_bound_of_continuousOn hH
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ t < δ := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (eventually_lt_nhds hδ)] with t ht htd
    exact ⟨ht, htd⟩
  have hball (x t : ℝ) (hx : |x - a| ≤ δ) (ht : |t| ≤ δ) :
      (x : ℂ) + (t : ℂ) * Complex.I ∈ Metric.closedBall (a : ℂ) (2 * δ) := by
    apply Metric.mem_closedBall.mpr
    exact (real_vertical_dist_le x a t).trans (by linarith)
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := 𝓝[>] (0 : ℝ))
    (F := fun t x : ℝ =>
      (H ((x : ℂ) + (t : ℂ) * Complex.I) - H ((x : ℂ) - (t : ℂ) * Complex.I)) * f x)
    (fun x : ℝ => (2 * C) * ‖f x‖) (f := fun _ : ℝ => (0 : ℂ)) ?_ ?_
      (f.integrable.norm.const_mul (2 * C)) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [] with t
    have hp : Continuous (fun x : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    have hn : Continuous (fun x : ℝ => (x : ℂ) - (t : ℂ) * Complex.I) := by fun_prop
    exact ((hHm.comp hp.measurable).sub (hHm.comp hn.measurable)).mul
      f.continuous.measurable |>.aestronglyMeasurable
  · filter_upwards [hevent] with t ht
    filter_upwards [] with x
    by_cases hx : f x = 0
    · simp only [hx, mul_zero, norm_zero, le_refl]
    · have hp := hC _ (hball x t (hf x hx) (by rw [abs_of_pos ht.1]; exact ht.2.le))
      have hn := hC _ (hball x (-t) (hf x hx) (by rw [abs_neg, abs_of_pos ht.1]; exact ht.2.le))
      have hbound : ‖H ((x : ℂ) + (t : ℂ) * Complex.I) -
          H ((x : ℂ) - (t : ℂ) * Complex.I)‖ ≤ 2 * C := by
        rw [show (x : ℂ) - (t : ℂ) * Complex.I =
          (x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact (norm_sub_le _ _).trans (by linarith)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
  · filter_upwards [] with x
    by_cases hx : f x = 0
    · simp only [hx, mul_zero]
      exact tendsto_const_nhds
    · have hb : (x : ℂ) ∈ Metric.ball (a : ℂ) (2 * δ) := by
        rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
        linarith [hf x hx]
      have hc := hH.continuousAt (Metric.closedBall_mem_nhds_of_mem hb)
      have hp : Tendsto (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I)
          (𝓝[>] 0) (𝓝 (x : ℂ)) := by
        have hc' : Continuous (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
        simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
          (hc'.tendsto 0).mono_left (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 0)
      have hn : Tendsto (fun t : ℝ => (x : ℂ) - (t : ℂ) * Complex.I)
          (𝓝[>] 0) (𝓝 (x : ℂ)) := by
        have hc' : Continuous (fun t : ℝ => (x : ℂ) - (t : ℂ) * Complex.I) := by fun_prop
        simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using
          (hc'.tendsto 0).mono_left (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 0)
      convert! ((hc.tendsto.comp hp).sub (hc.tendsto.comp hn)).mul_const (f x) using 1
      simp only [sub_self, zero_mul]

end

end MeyerGeneralProblem.StrongParity
