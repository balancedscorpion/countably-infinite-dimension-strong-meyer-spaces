module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalClassicalAdaptiveRadii
public import MeyerGeneralProblem.Hermite.Exhaustion

@[expose] public section

/-! Whole infinite original unit-ball exhaustion from actual shrinking residual bounds and full Schwartz Hermite expansion. Original weighted-TV hypotheses are retained. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- EVERY complete original SAME-N unit input on the actual infinite carrier is fixed by the SAME finite projection. -/
theorem originalClassicalStrongCarrier_unit_projection (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ originalStrongPairUnitBall (originalScheduledCommonCarrier originalClassicalAdaptiveBound) N) :
    T = originalScheduledAnchorProjection (originalCommonWindowBounds originalClassicalAdaptiveBound) (N + 1) T := by
  let U := T - originalScheduledAnchorProjection (originalCommonWindowBounds originalClassicalAdaptiveBound) (N + 1) T
  have hz (l : ℕ) : U (normalizedHermiteSchwartz l) = 0 := by
    have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have hle : ‖U (normalizedHermiteSchwartz l)‖ + ‖𝓕 U (normalizedHermiteSchwartz l)‖ ≤ 0 := by
      apply ge_of_tendsto hlim
      apply Filter.eventually_atTop.mpr
      refine ⟨max (N + 1) (l + 1), ?_⟩
      intro k hk
      exact (originalClassicalAdaptiveBound_residual k N l (by omega) (by omega) T hT).le
    apply norm_eq_zero.mp
    have h₁ := norm_nonneg (U (normalizedHermiteSchwartz l))
    have h₂ := norm_nonneg (𝓕 U (normalizedHermiteSchwartz l))
    linarith
  have hu : U = 0 := by
    ext f
    rw [temperedDistribution_apply_eq_tsum_hermiteCoefficients]
    simp only [hz, zero_mul, tsum_zero, zero_apply]
  exact sub_eq_zero.mp hu

end
end MeyerGeneralProblem.StrongParity
