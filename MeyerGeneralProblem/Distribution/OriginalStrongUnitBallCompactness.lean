module

public import MeyerGeneralProblem.Distribution.OriginalDualWeightedVariationRecovery

@[expose] public section

/-! Compactness of the COMPLETE ORIGINAL SAME-N strongly tempered Fourier-pair
TV-sum unit ball on an actual locally finite carrier. Compactness is in the
actual pointwise full-Schwartz tempered-distribution topology. BOTH original
variations are recovered internally from genuine compact C0 duals. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped FourierTransform

/-- The genuine weighted dual physical distribution map is continuous for EVERY full Schwartz observation. -/
theorem originalWeightedDualPhysicalDistribution_continuous (N : ℕ) :
    Continuous (originalWeightedDualPhysicalDistribution N) :=
  PointwiseConvergenceCLM.continuous_of_continuous_eval
    (originalWeightedDualPhysicalDistribution_eval_continuous N)

/-- The genuine weighted spectral map is continuous in the SAME full-Schwartz topology. -/
theorem originalWeightedDualSpectralDistribution_continuous (N : ℕ) :
    Continuous (originalWeightedDualSpectralDistribution N) :=
  PointwiseConvergenceCLM.continuous_of_continuous_eval
    (originalWeightedDualSpectralDistribution_eval_continuous N)

/-- ALL original same-N strong Fourier pairs on the actual carrier with the
SUM of their TWO original weighted absolute variations at most one. -/
def originalStrongPairUnitBall (S : LocallyFiniteCarrier) (N : ℕ) : Set (TemperedDistribution ℝ ℂ) :=
  {T | T ∈ stronglyTemperedAtomicAtExponent S N ∧ 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N ∧
    originalStrongPairVariation S N T ≤ 1}

/-- The COMPLETE original strong unit ball is EXACTLY the genuine compact carrier-dual image. -/
theorem originalStrongPairUnitBall_eq_supported_dual_image (S : LocallyFiniteCarrier) (N : ℕ) :
    originalStrongPairUnitBall S N = originalWeightedDualPhysicalDistribution N ''
      originalWeightedDualSupportedFourierPairBall S N := by
  ext T
  exact originalStrong_unit_pair_iff_supported_dual S N T

/-- The COMPLETE ORIGINAL TV-sum unit ball is compact in the actual full-Schwartz
distribution topology; no substituted norm, compactness or variation-recovery certificate is assumed. -/
theorem originalStrongPairUnitBall_isCompact (S : LocallyFiniteCarrier) (N : ℕ) :
    IsCompact (originalStrongPairUnitBall S N) := by
  rw [originalStrongPairUnitBall_eq_supported_dual_image]
  exact (originalWeightedDualSupportedFourierPairBall_isCompact S N).image
    (originalWeightedDualPhysicalDistribution_continuous N)

end
end MeyerGeneralProblem
