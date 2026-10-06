module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalNativeLaurentTransport
public import MeyerGeneralProblem.Distribution.CarrierInclusion

@[expose] public section

/-! Genuine ORIGINAL scheduled sources constructed from the FULL native slab.
Actual pushforward, its Fourier Jacobian, both original strong records and the
WHOLE common-module cut numerator are proved internally. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The actual scheduled block source with its exact physical Jacobian. -/
def originalScheduledNativeSource (bound : ℕ → ℕ) (i : ℕ)
    (r : productNumeratorIndex (originalReflectedOrderSchedule bound i) → ℂ) :
    TemperedDistribution ℝ ℂ :=
  originalJacobianNormalizedDilation (originalPrivateScale (originalReflectedPrimeSchedule bound i))
    (originalPrivateScale_pos _ (originalScheduledBlockPrime_pos bound i))
    (CompactOriginal.productPhysicalDistribution (originalScheduledParameterBlock bound i) r)

/-- Both ORIGINAL records of every full native source have explicit strong exponents. -/
theorem originalScheduledNativeSource_both_strong (bound : ℕ → ℕ) (i : ℕ)
    (r : productNumeratorIndex (originalReflectedOrderSchedule bound i) → ℂ) :
    originalScheduledNativeSource bound i r ∈ stronglyTemperedAtomicAtExponent
      (originalScheduledFullPhysicalCarrier bound i) ((originalReflectedOrderSchedule bound i - 1) + 2) ∧
    𝓕 (originalScheduledNativeSource bound i r) ∈ stronglyTemperedAtomicAtExponent
      (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i)
        (originalScheduledBlockPrime_pos bound i)) (originalReflectedOrderSchedule bound i + 3) := by
  exact originalJacobianNormalizedDilation_both_strong _ _ _ _ _ _ _
    (CompactOriginal.productPhysicalDistribution_mem_strongExponent _ r)
    (by rw [CompactOriginal.productPhysical_fourier_eq_spectral]
        exact CompactOriginal.productSpectralDistribution_mem_strongExponent _ r)

/-- The full actual physical roots support the WHOLE constructed source. -/
theorem originalScheduledNativeSource_atomicOnRoots (bound : ℕ → ℕ) (i : ℕ)
    (r : productNumeratorIndex (originalReflectedOrderSchedule bound i) → ℂ) :
    AtomicOnCarrier (originalScheduledFullPhysicalCarrier bound i)
      (originalScheduledNativeSource bound i r) :=
  hasLocallyAtomicAction_atomicOnCarrier _ _ (originalScheduledNativeSource_both_strong bound i r).1.1

/-- Its Fourier record is atomic on its full actual private cone, with zero once. -/
theorem originalScheduledNativeSource_fourier_atomicOnPrivateCone (bound : ℕ → ℕ) (i : ℕ)
    (r : productNumeratorIndex (originalReflectedOrderSchedule bound i) → ℂ) :
    AtomicOnCarrier (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i)
      (originalScheduledBlockPrime_pos bound i)) (𝓕 (originalScheduledNativeSource bound i r)) :=
  hasLocallyAtomicAction_atomicOnCarrier _ _ (originalScheduledNativeSource_both_strong bound i r).2.1

/-- EVERY full private cone embeds into the genuine common finite-prefix cone. -/
theorem originalScheduledFullPrivateCone_subset_prefixCone (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i.val)
      (originalScheduledBlockPrime_pos bound i.val)).carrier ⊆ (originalScheduledPrefixCone bound k).carrier :=
  originalPrivateSpectralCone_subset_divisible _ _ (originalScheduledBlockPrime_pos bound i.val)
    (originalScheduledPrefixDenominator_pos bound k) (originalScheduledBlockPrime_dvd_prefix bound k i)

/-- Every constructed Fourier record is genuinely atomic on the whole common cone. -/
theorem originalScheduledNativeSource_fourier_atomicOnPrefixCone (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (r : productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ) :
    AtomicOnCarrier (originalScheduledPrefixCone bound k) (𝓕 (originalScheduledNativeSource bound i.val r)) :=
  (originalScheduledNativeSource_fourier_atomicOnPrivateCone bound i.val r).mono
    (originalScheduledFullPrivateCone_subset_prefixCone bound k i)

/-- EVERY common label in a full private cone has a literal native preimage. -/
theorem originalScheduledFullPrivateCone_common_label (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (z : ℤ × ℤ)
    (hz : originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z ∈
      (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i.val)
        (originalScheduledBlockPrime_pos bound i.val)).carrier) :
    z ∈ Set.range (originalIntegerCoordinateDilation (originalScheduledPrefixCoordinateDilation bound k i)) := by
  obtain ⟨w, hw⟩ := originalPrivateSpectralCone_subset_module _ (originalScheduledBlockPrime_pos bound i.val) hz
  refine ⟨w, originalScaledModuleFrequencyHom_injective _
    (originalPrivateScale_pos _ (originalScheduledPrefixDenominator_pos bound k)).ne' ?_⟩
  rw [originalScheduledPrefixFrequency_coordinateDilation]
  exact hw

/-- The WHOLE actual Fourier array is the native array embedded at exact labels,
including all common labels outside the private module as genuine zeros. -/
theorem originalScheduledNativeSource_originalFourierArray (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (r : productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ) :
    originalFourierArray
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
      (originalScheduledPrefixCone bound k) (originalScheduledNativeSource bound i.val r) =
    originalArrayEmbedding (originalIntegerCoordinateDilation (originalScheduledPrefixCoordinateDilation bound k i))
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
        (CompactOriginal.productPhysicalDistribution (originalScheduledParameterBlock bound i.val) r)) := by
  classical
  let e := originalIntegerCoordinateDilation (originalScheduledPrefixCoordinateDilation bound k i)
  have he : Function.Injective e := originalIntegerCoordinateDilation_injective _
    (originalScheduledPrefixCoordinateDilation_pos bound k i)
  funext z
  change extendedAtomicCoefficient _ _ _ = _
  rw [extendedAtomicCoefficient_on_larger_carrier _ _
    (originalScheduledFullPrivateCone_subset_prefixCone bound k i) _
    (originalScheduledNativeSource_fourier_atomicOnPrivateCone bound i.val r)]
  by_cases hz : z ∈ Set.range e
  · obtain ⟨w, rfl⟩ := hz
    rw [originalArrayEmbedding_apply e he, originalScheduledPrefixFrequency_coordinateDilation]
    unfold originalScheduledNativeSource
    rw [originalJacobianNormalizedDilation_fourier]
    change extendedAtomicCoefficient
      (spectralConeCarrier.dilate _ _) (combDistributionDilation _ _ _) _ = _
    have hfreq : originalScaledModuleFrequencyHom
        (originalPrivateScale (originalReflectedPrimeSchedule bound i.val)) w =
        (originalPrivateScale (originalReflectedPrimeSchedule bound i.val))⁻¹ * rankTwoFrequencyHom w := by
      change rankTwoFrequencyHom w / _ = _
      rw [div_eq_mul_inv, mul_comm]
    rw [hfreq]
    have hFT : AtomicOnCarrier spectralConeCarrier
        (𝓕 (CompactOriginal.productPhysicalDistribution (originalScheduledParameterBlock bound i.val) r)) := by
      rw [CompactOriginal.productPhysical_fourier_eq_spectral]
      exact CompactOriginal.productSpectralDistribution_atomicOnCarrier _ r
    exact extendedAtomicCoefficient_dilation spectralConeCarrier _
      (inv_pos.mpr (originalPrivateScale_pos _ (originalScheduledBlockPrime_pos bound i.val))) _ hFT
      (rankTwoFrequencyHom w)
  · have hx : originalScaledModuleFrequencyHom
        (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z ∉
        (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i.val)
          (originalScheduledBlockPrime_pos bound i.val)).carrier :=
      fun h => hz (originalScheduledFullPrivateCone_common_label bound k i z h)
    rw [originalArrayEmbedding_zero_off_range e _ z hz]
    exact dite_eq_right hx

/-- The full actual block cut numerator is the literal dilated native slab,
derived from actual source coefficients and the native Fourier pair. -/
theorem originalScheduledNativeSource_cutNumerator (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (r : productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ) :
    cutArrayNumerator
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
      (originalPositiveLaurentEmbedding (originalScheduledBlockPositivePolynomial bound k i)).coeff 0
      (originalFourierArray
        (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
        (originalScheduledPrefixCone bound k) (originalScheduledNativeSource bound i.val r)) =
      (originalPositiveLaurentEmbedding
        (originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
          (originalPhasedSlabPositivePolynomial (originalReflectedOrderSchedule bound i.val) r))).coeff := by
  rw [originalScheduledNativeSource_originalFourierArray,
    originalScheduledBlockPositivePolynomial_laurent_coeff,
    originalArrayEmbedding_cutNumerator _ (originalIntegerCoordinateDilation_injective _
      (originalScheduledPrefixCoordinateDilation_pos bound k i)) _ _
      (originalScheduledPrefixFrequency_coordinateDilation bound k i)]
  unfold cutArrayNumerator
  rw [originalScaledModule_positiveCut_zero _
    (originalPrivateScale_pos _ (originalScheduledBlockPrime_pos bound i.val))]
  change originalArrayEmbedding _ (cutArrayNumerator rankTwoFrequencyHom _ 0 _) = _
  rw [CompactOriginal.productPhysical_cutNumerator_eq_slab,
    originalArrayEmbedding_finite _ (originalIntegerCoordinateDilation_injective _
      (originalScheduledPrefixCoordinateDilation_pos bound k i)),
    originalPositiveLaurentEmbedding_dilation, originalPhasedSlabPositivePolynomial_laurent]
  rfl

end
end MeyerGeneralProblem.StrongParity
