module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalAnchorProjection
public import MeyerGeneralProblem.Distribution.OriginalWindowResidualBounds

@[expose] public section

/-! A single ACTUAL root-anchor projection at r > max M N fixes EVERY
complete original (M,N) finite-prefix source, independently of prefix length.
The original private-mass cutoff supplies the truncation internally. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The actual anchor projection is continuous in the full Schwartz pointwise distribution topology. -/
theorem originalScheduledAnchorProjection_continuous (bound : ℕ → ℕ) (r : ℕ) :
    Continuous (originalScheduledAnchorProjection bound r) := by
  have he (i : Fin r) : Continuous (fun T : TemperedDistribution ℝ ℂ =>
      T (originalScheduledPrefixAnchorTest bound r i)) :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ
      (originalScheduledPrefixAnchorTest bound r i)).continuous
  apply PointwiseConvergenceCLM.continuous_of_continuous_eval
  intro f
  simp only [originalScheduledAnchorProjection, add_apply, FourierTransform.fourierInv_sum,
    FourierTransform.fourierInv_smul, _root_.sum_apply, smul_apply, smul_eq_mul]
  exact (continuous_finsetSum _ (fun i _ => (he i).mul continuous_const)).add
    (continuous_finsetSum _ (fun i _ =>
      ((he i).comp FourierTransform.continuous_fourier).mul continuous_const))

/-- The ACTUAL anchor projection as a continuous complex linear operator. -/
def originalScheduledAnchorProjectionCLM (bound : ℕ → ℕ) (r : ℕ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ where
  toLinearMap := originalScheduledAnchorProjectionLinearMap bound r
  cont := originalScheduledAnchorProjection_continuous bound r

/-- The actual anchor operator is an idempotent on ALL full tempered distributions. -/
theorem originalScheduledAnchorProjection_idempotent (bound : ℕ → ℕ) (r : ℕ)
    (T : TemperedDistribution ℝ ℂ) :
    originalScheduledAnchorProjection bound r (originalScheduledAnchorProjection bound r T) =
      originalScheduledAnchorProjection bound r T :=
  originalScheduledAnchorProjection_mixed_sum bound r
    (fun i => T (originalScheduledPrefixAnchorTest bound r i))
    (fun i => 𝓕 T (originalScheduledPrefixAnchorTest bound r i))

/-- The SAME actual r-mode projection fixes any larger mixed combination
whose coefficients beyond r are zero. This lemma is used with the internally
proved ORIGINAL exponent cutoff below. -/
theorem originalScheduledAnchorProjection_truncated_mixed_sum (bound : ℕ → ℕ) (k r : ℕ)
    (a b : Fin k → ℂ) (hz : ∀ i : Fin k, r ≤ i.val → a i = 0 ∧ b i = 0) :
    originalScheduledAnchorProjection bound r
      ((∑ i : Fin k, a i • originalScheduledPrivateLineSource bound i.val) +
        𝓕⁻ (∑ i : Fin k, b i • originalScheduledPrivateLineSource bound i.val)) =
      (∑ i : Fin k, a i • originalScheduledPrivateLineSource bound i.val) +
        𝓕⁻ (∑ i : Fin k, b i • originalScheduledPrivateLineSource bound i.val) := by
  have hzero (t : TemperedDistribution ℝ ℂ) : (0 : ℂ) • t = 0 := zero_smul ℂ t
  have hi : 𝓕⁻ (∑ i : Fin k, b i • originalScheduledPrivateLineSource bound i.val) =
      ∑ i : Fin k, b i • 𝓕⁻ (originalScheduledPrivateLineSource bound i.val) := by
    rw [FourierTransform.fourierInv_sum]
    simp only [FourierTransform.fourierInv_smul]
  change originalScheduledAnchorProjectionLinearMap bound r _ = _
  rw [hi, map_add, map_sum, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    by_cases hir : i.val < r
    · exact congrArg (fun T => a i • T)
        (originalScheduledAnchorProjection_native bound r ⟨i.val, hir⟩)
    · rw [(hz i (Nat.le_of_not_gt hir)).1, hzero, hzero]
  · apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    by_cases hir : i.val < r
    · exact congrArg (fun T => b i • T)
        (originalScheduledAnchorProjection_inverse bound r ⟨i.val, hir⟩)
    · rw [(hz i (Nat.le_of_not_gt hir)).2, hzero, hzero]

/-- BOTH ORIGINAL exponents force the SAME r-mode projection to fix EVERY
complete finite-prefix input, regardless of its prefix length. No cutoff or
finite-prefix exhaustion certificate is supplied. -/
theorem originalScheduledAnchorProjection_fixed_exponents (bound : ℕ → ℕ) (k M N r : ℕ)
    (hr : max M N < r) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    originalScheduledAnchorProjection bound r T = T := by
  obtain ⟨a, b, he, hz⟩ := originalScheduledPrefix_mixed_private_lines_uniform_index_bound
    bound k M N T hT hF
  rw [he]
  exact originalScheduledAnchorProjection_truncated_mixed_sum bound k r a b
    (fun i hi => hz i (hr.trans_le hi))

/-- In particular, a SINGLE actual N+1-mode projection fixes the COMPLETE
original SAME-N unit ball of EVERY finite prefix. -/
theorem originalScheduledAnchorProjection_original_unit_prefix (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ originalStrongPairUnitBall (originalScheduledPrefixCarrier bound k) N) :
    originalScheduledAnchorProjection bound (N + 1) T = T :=
  originalScheduledAnchorProjection_fixed_exponents bound k N N (N + 1)
    (by omega) T hT.1 hT.2.1

end
end MeyerGeneralProblem.StrongParity
