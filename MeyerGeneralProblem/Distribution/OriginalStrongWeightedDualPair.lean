module

public import MeyerGeneralProblem.Distribution.OriginalWeightedDualDistribution

@[expose] public section

/-! BOTH original strongly tempered records enter the actual compact weighted
dual Fourier graph internally. Their WHOLE distributions are recovered, and
the pair dual norm is bounded by the sum of BOTH SAME-N original variations. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty FourierTransform

/-- The actual sum of the TWO original same-N weighted absolute variations. -/
def originalStrongPairVariation (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ) : ℝ :=
  (∑' x : S.subtype, stronglyTemperedCoefficientTerm S N T x) +
    ∑' x : S.subtype, stronglyTemperedCoefficientTerm S N (𝓕 T) x

/-- The original two-record weighted variation is nonnegative. -/
theorem originalStrongPairVariation_nonneg (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ) :
    0 ≤ originalStrongPairVariation S N T := by
  apply add_nonneg <;> apply tsum_nonneg <;> intro x <;> unfold stronglyTemperedCoefficientTerm <;> positivity

/-- The ACTUAL two original weighted records as a single dual of the C0 product with max norm. -/
def originalStrongPairC0Dual (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) :
    StrongDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) :=
  (originalStrongAtomicC0Dual S N T hT).comp (ContinuousLinearMap.fst ℂ C₀(ℝ, ℂ) C₀(ℝ, ℂ)) +
    (originalStrongAtomicC0Dual S N (𝓕 T) hF).comp (ContinuousLinearMap.snd ℂ C₀(ℝ, ℂ) C₀(ℝ, ℂ))

/-- ALL C0 pair observations evaluate the TWO literal original weighted records. -/
theorem originalStrongPairC0Dual_apply (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N)
    (g : C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) :
    originalStrongPairC0Dual S N T hT hF g =
      originalStrongAtomicC0Dual S N T hT g.1 + originalStrongAtomicC0Dual S N (𝓕 T) hF g.2 := rfl

/-- The pair norm is bounded by BOTH ORIGINAL variations at SAME N, derived from actual records. -/
theorem originalStrongPairC0Dual_norm_le (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) :
    ‖originalStrongPairC0Dual S N T hT hF‖ ≤ originalStrongPairVariation S N T := by
  apply ContinuousLinearMap.opNorm_le_bound _ (originalStrongPairVariation_nonneg S N T)
  intro g
  rw [originalStrongPairC0Dual_apply]
  have hp := (originalStrongAtomicC0Dual S N T hT).le_opNorm g.1
  have hs := (originalStrongAtomicC0Dual S N (𝓕 T) hF).le_opNorm g.2
  have hpV := originalStrongAtomicC0Dual_norm_le S N T hT
  have hsV := originalStrongAtomicC0Dual_norm_le S N (𝓕 T) hF
  calc
    _ ≤ ‖originalStrongAtomicC0Dual S N T hT g.1‖ + ‖originalStrongAtomicC0Dual S N (𝓕 T) hF g.2‖ := norm_add_le _ _
    _ ≤ ‖originalStrongAtomicC0Dual S N T hT‖ * ‖g.1‖ +
        ‖originalStrongAtomicC0Dual S N (𝓕 T) hF‖ * ‖g.2‖ := add_le_add hp hs
    _ ≤ ‖originalStrongAtomicC0Dual S N T hT‖ * ‖g‖ +
        ‖originalStrongAtomicC0Dual S N (𝓕 T) hF‖ * ‖g‖ := by
      gcongr
      · exact _root_.norm_fst_le g
      · exact _root_.norm_snd_le g
    _ ≤ _ := by
      unfold originalStrongPairVariation
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hpV (norm_nonneg g))
        (mul_le_mul_of_nonneg_right hsV (norm_nonneg g))

/-- The internally constructed actual pair dual recovers the WHOLE physical distribution. -/
theorem originalStrongPairC0Dual_physical (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) :
    originalWeightedDualPhysicalDistribution N (originalStrongPairC0Dual S N T hT hF).toWeakDual = T := by
  ext f
  rw [originalWeightedDualPhysicalDistribution_apply, StrongDual.toWeakDual_apply,
    originalStrongPairC0Dual_apply]
  change originalStrongAtomicC0Dual S N T hT (originalWeightedSchwartzC0 N f) +
    originalStrongAtomicC0Dual S N (𝓕 T) hF 0 = T f
  rw [map_zero, add_zero]
  exact originalStrongAtomicC0Dual_schwartz S N T hT f

/-- The internally constructed actual pair dual recovers the WHOLE original Fourier distribution. -/
theorem originalStrongPairC0Dual_spectral (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) :
    originalWeightedDualSpectralDistribution N (originalStrongPairC0Dual S N T hT hF).toWeakDual = 𝓕 T := by
  ext f
  rw [originalWeightedDualSpectralDistribution_apply, StrongDual.toWeakDual_apply,
    originalStrongPairC0Dual_apply]
  change originalStrongAtomicC0Dual S N T hT 0 +
    originalStrongAtomicC0Dual S N (𝓕 T) hF (originalWeightedSchwartzC0 N f) = (𝓕 T) f
  rw [map_zero, zero_add]
  exact originalStrongAtomicC0Dual_schwartz S N (𝓕 T) hF f

/-- EVERY original same-N weighted Fourier pair internally satisfies the genuine closed Fourier graph. -/
theorem originalStrongPairC0Dual_fourierGraph (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) :
    originalWeightedDualSpectralDistribution N (originalStrongPairC0Dual S N T hT hF).toWeakDual =
      𝓕 (originalWeightedDualPhysicalDistribution N (originalStrongPairC0Dual S N T hT hF).toWeakDual) := by
  rw [originalStrongPairC0Dual_physical, originalStrongPairC0Dual_spectral]

/-- EVERY original same-N unit-variation pair enters the ACTUAL compact dual Fourier ball internally. -/
theorem originalStrongPairC0Dual_mem_ball (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N)
    (hunit : originalStrongPairVariation S N T ≤ 1) :
    (originalStrongPairC0Dual S N T hT hF).toWeakDual ∈ originalWeightedDualFourierPairBall N := by
  refine ⟨?_, originalStrongPairC0Dual_fourierGraph S N T hT hF⟩
  change WeakDual.toStrongDual (originalStrongPairC0Dual S N T hT hF).toWeakDual ∈ Metric.closedBall 0 1
  rw [StrongDual.toStrongDual_toWeakDual, Metric.mem_closedBall]
  exact (dist_zero_right (originalStrongPairC0Dual S N T hT hF)).le.trans
    ((originalStrongPairC0Dual_norm_le S N T hT hF).trans hunit)

/-- BOTH ORIGINAL strong records and their actual unit-variation bound ALONE
produce a compact-ball member recovering the entire original Fourier pair. -/
theorem originalStrongPair_exists_weighted_dual_ball (S : LocallyFiniteCarrier) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) (hunit : originalStrongPairVariation S N T ≤ 1) :
    ∃ q ∈ originalWeightedDualFourierPairBall N,
      originalWeightedDualPhysicalDistribution N q = T ∧ originalWeightedDualSpectralDistribution N q = 𝓕 T :=
  ⟨_, originalStrongPairC0Dual_mem_ball S N T hT hF hunit,
    originalStrongPairC0Dual_physical S N T hT hF, originalStrongPairC0Dual_spectral S N T hT hF⟩

end
end MeyerGeneralProblem
