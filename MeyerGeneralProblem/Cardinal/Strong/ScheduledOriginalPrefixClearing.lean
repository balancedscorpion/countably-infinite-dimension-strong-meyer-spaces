module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixPolynomial

@[expose] public section

/-! Actual zero-output clearing and ALL original module-label recurrence for
EVERY complete scheduled mixed-prefix strong pair. The common denominator,
positive polynomial motif, all complete roots/supports and EVERY module-avoidance
premise are supplied internally from the coupled construction. This precedes,
and does not assume, numerator reconstruction or infinite exhaustion. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The actual original cleared Fourier distribution of a COMPLETE scheduled prefix. -/
def originalScheduledPrefixClearedFourierDistribution (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ) : TemperedDistribution ℝ ℂ :=
  originalStrongRootClearedFourierDistribution
    (originalPrivateScale (originalScheduledPrefixDenominator bound k))
    (originalScheduledPrefixPolynomialCoordinates bound k)
    (originalScheduledPrefixPolynomialCoefficient bound k) T

/-- Genuine zero-output clearing for ALL original strong pairs, with ALL construction data internal. -/
theorem originalScheduledPrefixClearedFourierDistribution_eq_zero (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    originalScheduledPrefixClearedFourierDistribution bound k T = 0 := by
  exact originalStrongRootClearedFourierDistribution_eq_zero (originalScheduledPrefixCarrier bound k)
    (originalScheduledPrefixRootSet bound k) (originalScheduledPrefixDenominator bound k)
    (originalScheduledPrefixDenominator_pos bound k)
    (originalScheduledPrefixPolynomialCoordinates bound k) (originalScheduledPrefixPolynomialCoefficient bound k)
    (originalScheduledPrefixCarrier_subset_roots_union_cone bound k)
    (originalScheduledPrefixPolynomial_vanishes bound k) M N T hT hF

/-- ALL original integer-label equations, including EVERY exterior quadrant, before reconstruction. -/
theorem originalScheduledPrefix_all_integer_label_recurrence (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N)
    (z : ℤ × ℤ) :
    ∑ i : OriginalScheduledPrefixMotif bound k,
      originalScheduledPrefixPolynomialCoefficient bound k i *
      extendedAtomicCoefficient (originalScheduledPrefixCarrier bound k) (𝓕 T)
        (originalScaledModuleFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k))
          (z - originalPositivePolynomialIntegerCoordinates (originalScheduledPrefixPolynomialCoordinates bound k) i)) = 0 := by
  exact originalStrongClearing_all_integer_label_recurrence (originalScheduledPrefixCarrier bound k)
    (originalScheduledPrefixRootSet bound k) (originalScheduledPrefixDenominator bound k)
    (originalScheduledPrefixDenominator_pos bound k)
    (originalScheduledPrefixPolynomialCoordinates bound k) (originalScheduledPrefixPolynomialCoefficient bound k)
    (originalScheduledPrefixCarrier_subset_roots_union_cone bound k)
    (originalScheduledPrefixPolynomial_vanishes bound k)
    (originalScheduledPrefixPolynomial_nonzero_on_module bound k) M N T hT hF z

/-- Actual clearing of the COMPLETE finite-prefix strong Meyer space, choosing both exponents internally. -/
theorem originalScheduledPrefixClearedFourierDistribution_complete_strong (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    originalScheduledPrefixClearedFourierDistribution bound k T = 0 := by
  obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT.1
  obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hT.2
  exact originalScheduledPrefixClearedFourierDistribution_eq_zero bound k M N T hM hN

/-- The COMPLETE original strong finite-prefix space satisfies ALL exterior recurrence equations. -/
theorem originalScheduledPrefix_complete_strong_recurrence (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (z : ℤ × ℤ) :
    ∑ i : OriginalScheduledPrefixMotif bound k,
      originalScheduledPrefixPolynomialCoefficient bound k i *
      extendedAtomicCoefficient (originalScheduledPrefixCarrier bound k) (𝓕 T)
        (originalScaledModuleFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k))
          (z - originalPositivePolynomialIntegerCoordinates (originalScheduledPrefixPolynomialCoordinates bound k) i)) = 0 := by
  obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT.1
  obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hT.2
  exact originalScheduledPrefix_all_integer_label_recurrence bound k M N T hM hN z

end
end MeyerGeneralProblem.StrongParity
