module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.PhysicalDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductFourierPair
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPoleMass
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.QuotientTubeSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralConeIndex
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.OriginalUpperTube

@[expose] public section

/-! Complete original OriginalUpperTube for actual compact parameter blocks.
Every original supported pair is retained, without a constructed-image premise. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open scoped FourierTransform

theorem productPhysical_originalFourierArray_positive {s : ℕ} (block : CompactOriginalParameterBlock s)
    (r : productNumeratorIndex s → ℂ) (p : ℕ × ℕ) :
    originalFourierArray rankTwoFrequencyHom spectralConeCarrier
      (productPhysicalDistribution block r) (natPairIntegerIndex p) =
        productConeIndexCoefficient block r (.inl p) := by
  classical
  unfold originalFourierArray
  rw [rankTwoFrequencyHom_natPair, productPhysical_fourier_eq_spectral]
  have hx : positiveConeFrequency p ∈ spectralConeCarrier.carrier :=
    (spectralConeIndexPoint (.inl p)).property
  unfold extendedAtomicCoefficient
  rw [dite_eq_left hx]
  exact (productSpectralDistribution_isolation block r (spectralConeIndexPoint (.inl p))).trans
    (productSpectralCoefficient_at_label block r (.inl p))

theorem productPhysical_originalPositiveCut_at_natPair {s : ℕ} (block : CompactOriginalParameterBlock s)
    (r : productNumeratorIndex s → ℂ) (p : ℕ × ℕ) :
    arrayPositiveCut rankTwoFrequencyHom 0
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
        (productPhysicalDistribution block r)) (natPairIntegerIndex p) =
      productConeIndexCoefficient block r (.inl p) := by
  classical
  unfold arrayPositiveCut
  rw [ite_eq_left (by rw [rankTwoFrequencyHom_natPair]; exact positiveConeFrequency_nonneg p)]
  exact productPhysical_originalFourierArray_positive block r p

/-- The actual original integer array has the retained quotient as its upper
half-plane sum. Every lattice point outside the positive cone has coefficient zero. -/
theorem productPhysical_originalPositiveCut_hasSum {s : ℕ} (block : CompactOriginalParameterBlock s)
    (r : productNumeratorIndex s → ℂ) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun n : ℤ × ℤ =>
      arrayPositiveCut rankTwoFrequencyHom 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
          (productPhysicalDistribution block r)) n *
        rankTwoEntireCharacter z (Multiplicative.ofAdd n))
      (complexProductSlabQuotient block r z) := by
  have hzero (n : ℤ × ℤ) (hn : n ∉ Set.range natPairIntegerIndex) :
      arrayPositiveCut rankTwoFrequencyHom 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
          (productPhysicalDistribution block r)) n *
        rankTwoEntireCharacter z (Multiplicative.ofAdd n) = 0 := by
    have hc : arrayPositiveCut rankTwoFrequencyHom 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
          (productPhysicalDistribution block r)) n = 0 := by
      by_contra hc
      exact hn ((natPairIntegerIndex_range n).mpr
        (originalPositiveCut_coordinate_nonneg _ hc))
    rw [hc, zero_mul]
  apply (natPairIntegerIndex_injective.hasSum_iff hzero).mp
  convert! productUpperTube_hasSum block r hz using 1
  · funext p
    simp only [Function.comp_def, productPhysical_originalPositiveCut_at_natPair,
      rankTwoEntireCharacter_apply, rankTwoFrequencyHom_natPair]

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
