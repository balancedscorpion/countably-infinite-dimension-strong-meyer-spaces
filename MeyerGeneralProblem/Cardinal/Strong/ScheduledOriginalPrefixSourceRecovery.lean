module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixSpectralRecord
public import MeyerGeneralProblem.Distribution.SimpleFiniteAnnihilatorRecovery

@[expose] public section

/-! A GENUINE original mixed-prefix root/cone Fourier pair is recovered internally.
The actual inverse Fourier transform of the weighted original module record is
annihilated by the full real-simple-root mixed product. Compact smooth division
proves value-only atomicity BEFORE any literal physical restriction is asserted. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The actual inverse Fourier transform of the original weighted module record. -/
def originalScheduledPrefixRootSource (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    TemperedDistribution ℝ ℂ := 𝓕⁻ (originalScheduledPrefixModuleSpectralRecord bound k N T hF)

/-- Its Fourier transform is the GENUINE weighted original module record, as whole distributions. -/
theorem originalScheduledPrefixRootSource_fourier (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    𝓕 (originalScheduledPrefixRootSource bound k N T hF) =
      originalScheduledPrefixModuleSpectralRecord bound k N T hF := FourierTransform.fourier_fourierInv_eq _

/-- ALL actual recurrence rows annihilate this genuine inverse transform with the full mixed symbol. -/
theorem originalScheduledPrefixRootSource_annihilated (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    finiteExponentialMultiplication
      (originalPositivePolynomialFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k))
        (originalScheduledPrefixPolynomialCoordinates bound k))
      (originalScheduledPrefixPolynomialCoefficient bound k)
      (originalScheduledPrefixRootSource bound k N T hF) = 0 := by
  have hf : 𝓕 (finiteExponentialMultiplication
      (originalPositivePolynomialFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k))
        (originalScheduledPrefixPolynomialCoordinates bound k))
      (originalScheduledPrefixPolynomialCoefficient bound k)
      (originalScheduledPrefixRootSource bound k N T hF)) = 0 := by
    rw [fourier_finiteExponentialMultiplication, originalScheduledPrefixRootSource_fourier,
      originalScheduledPrefixModuleSpectralRecord_annihilated bound k M N T hT hF]
  simpa only [FourierTransform.fourierInv_fourier_eq, FourierTransform.fourierInv_zero] using
    congrArg (fun U : TemperedDistribution ℝ ℂ => 𝓕⁻ U) hf

/-- EVERY actual original strong pair supplies a recovered value-only source on ALL complete roots. -/
theorem originalScheduledPrefixRootSource_atomicOnRoots (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k)
      (originalScheduledPrefixRootSource bound k N T hF) := by
  have he : finitePositiveExponentialSymbol
      (originalPositivePolynomialFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k))
        (originalScheduledPrefixPolynomialCoordinates bound k))
      (originalScheduledPrefixPolynomialCoefficient bound k) = originalScheduledPrefixRealSymbol bound k :=
    funext (originalScheduledPrefixPolynomial_finiteSymbol bound k)
  apply atomicOnCarrier_of_zero_simple_finiteExponentialMultiplication
    (originalScheduledPrefixFullRootCarrier bound k) _ _ _ _ _
    (originalScheduledPrefixRootSource_annihilated bound k M N T hT hF)
  · intro x hx
    rw [he] at hx
    exact (originalScheduledPrefixRealSymbol_zero_iff bound k x).mp hx
  · rw [he]
    exact originalScheduledPrefixRealSymbol_deriv_ne_zero bound k

/-- The recovered source has a genuine cone Fourier record with no raw-pair restriction premise. -/
theorem originalScheduledPrefixRootSource_fourier_atomicOnCone (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    AtomicOnCarrier (originalScheduledPrefixCone bound k)
      (𝓕 (originalScheduledPrefixRootSource bound k N T hF)) := by
  rw [originalScheduledPrefixRootSource_fourier]
  exact originalScheduledPrefixModuleSpectralRecord_atomicOnCone bound k N T hF

/-- Subtracting the recovered GENUINE source leaves a root-supported original Fourier record. -/
theorem originalScheduledPrefixRootSource_complement_fourier_atomicOnRoots (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k)
      (𝓕 (T - originalScheduledPrefixRootSource bound k N T hF)) := by
  change AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k)
    (temperedFourierLinearMap (T - originalScheduledPrefixRootSource bound k N T hF))
  rw [map_sub, temperedFourierLinearMap_apply, temperedFourierLinearMap_apply,
    originalScheduledPrefixRootSource_fourier]
  exact originalScheduledPrefixModuleSpectralRecord_complement_atomicOnRoots bound k N T hF

/-- The COMPLETE original prefix strong space supplies both exponents and a GENUINE
root/cone source internally; physical literalness is proved only after subtraction. -/
theorem originalScheduledPrefix_complete_strong_root_source_exists (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ N : ℕ, ∃ ρ : TemperedDistribution ℝ ℂ,
      AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k) ρ ∧
      AtomicOnCarrier (originalScheduledPrefixCone bound k) (𝓕 ρ) ∧
      𝓕 ρ ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N ∧
      (∀ z : ℤ × ℤ, extendedAtomicCoefficient (originalScheduledPrefixCarrier bound k) (𝓕 ρ)
        (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z) =
          originalScheduledPrefixFourierArray bound k T z) ∧
      AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k) (𝓕 (T - ρ)) := by
  obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT.1
  obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hT.2
  have hM' : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M := hM
  have hN' : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N := hN
  refine ⟨N, originalScheduledPrefixRootSource bound k N T hN',
    originalScheduledPrefixRootSource_atomicOnRoots bound k M N T hM' hN',
    originalScheduledPrefixRootSource_fourier_atomicOnCone bound k N T hN', ?_, ?_,
    originalScheduledPrefixRootSource_complement_fourier_atomicOnRoots bound k N T hN'⟩
  · rw [originalScheduledPrefixRootSource_fourier]
    exact originalScheduledPrefixModuleSpectralRecord_mem_strongExponent bound k N T hN'
  · rw [originalScheduledPrefixRootSource_fourier]
    exact originalScheduledPrefixModuleSpectralRecord_coefficient bound k N T hN'

end
end MeyerGeneralProblem.StrongParity
