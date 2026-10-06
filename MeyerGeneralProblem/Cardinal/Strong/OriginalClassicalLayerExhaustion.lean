module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalClassicalUnitExhaustion

@[expose] public section

/-! Normalization of BOTH original weighted records and whole infinite fixed-exponent exhaustion. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The actual sum of BOTH original weighted variations scales by the absolute value of the complex scalar. -/
theorem originalStrongPairVariation_smul (S : LocallyFiniteCarrier) (N : ℕ)
    (a : ℂ) (T : TemperedDistribution ℝ ℂ) :
    originalStrongPairVariation S N (a • T) = ‖a‖ * originalStrongPairVariation S N T := by
  simp only [originalStrongPairVariation, stronglyTemperedCoefficientTerm,
    FourierTransform.fourier_smul, smul_apply, norm_smul, mul_div_assoc,
    tsum_mul_left, mul_add]

/-- EVERY complete original SAME-N input on the actual infinite carrier is fixed, by internal normalization. -/
theorem originalClassicalStrongCarrier_projection (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledCommonCarrier originalClassicalAdaptiveBound) N)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledCommonCarrier originalClassicalAdaptiveBound) N) :
    T = originalScheduledAnchorProjection (originalCommonWindowBounds originalClassicalAdaptiveBound) (N + 1) T := by
  let S := originalScheduledCommonCarrier originalClassicalAdaptiveBound
  let V := originalStrongPairVariation S N T
  have hV : 0 ≤ V := originalStrongPairVariation_nonneg S N T
  have hp : 0 < V + 1 := by linarith
  let a : ℂ := ((V + 1)⁻¹ : ℝ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (inv_ne_zero (ne_of_gt hp))
  have hn : ‖a‖ = (V + 1)⁻¹ := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  have hu : a • T ∈ originalStrongPairUnitBall S N := by
    refine ⟨(stronglyTemperedAtomicAtExponent S N).smul_mem a hT, ?_, ?_⟩
    · rw [FourierTransform.fourier_smul]
      exact (stronglyTemperedAtomicAtExponent S N).smul_mem a hF
    · rw [originalStrongPairVariation_smul, hn]
      change (V + 1)⁻¹ * V ≤ 1
      calc
        _ ≤ (V + 1)⁻¹ * (V + 1) := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hp.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hp)
  have h := originalClassicalStrongCarrier_unit_projection N (a • T) hu
  rw [originalScheduledAnchorProjection_smul] at h
  have he := congrArg (fun U : TemperedDistribution ℝ ℂ => a⁻¹ • U) h
  simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using he

end
end MeyerGeneralProblem.StrongParity
