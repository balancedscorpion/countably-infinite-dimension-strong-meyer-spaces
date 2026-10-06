module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalNativeSources
public import MeyerGeneralProblem.Distribution.CarrierUnion

@[expose] public section

/-! Exact whole-record source algebra and the actual full-prefix annihilator.
Carrier choices retain the intrinsic coefficients; genuine finite source sums
retain the full convolution numerators, with no supplied reconstruction. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped FourierTransform

/-- Two genuine atomic carriers give the same intrinsic coefficient at EVERY point. -/
theorem extendedAtomicCoefficient_two_carriers (S U : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hS : AtomicOnCarrier S T) (hU : AtomicOnCarrier U T) (x : ℝ) :
    extendedAtomicCoefficient S T x = extendedAtomicCoefficient U T x :=
  (extendedAtomicCoefficient_on_larger_carrier S (S.union U) Set.subset_union_left T hS x).symm.trans
    (extendedAtomicCoefficient_on_larger_carrier U (S.union U) Set.subset_union_right T hU x)

/-- The actual Fourier-array cut numerator is a genuine linear map of whole sources. -/
def originalSourceCutNumeratorLinearMap {G : Type*} [AddCommGroup G]
    (L : G →+ ℝ) (S : LocallyFiniteCarrier) (p : G →₀ ℂ) (s : ℝ) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] (G → ℂ) where
  toFun T := cutArrayNumerator L p s (originalFourierArray L S T)
  map_add' T U := by rw [originalFourierArray_add, cutArrayNumerator_add]
  map_smul' c T := by rw [originalFourierArray_smul, cutArrayNumerator_smul]; rfl

/-- A finite sum of actual sources has the sum of its WHOLE cut numerators. -/
theorem originalSourceCutNumerator_sum {G ι : Type*} [AddCommGroup G] [Fintype ι]
    (L : G →+ ℝ) (S : LocallyFiniteCarrier) (p : G →₀ ℂ) (s : ℝ)
    (T : ι → TemperedDistribution ℝ ℂ) :
    cutArrayNumerator L p s (originalFourierArray L S (∑ i, T i)) =
      ∑ i, cutArrayNumerator L p s (originalFourierArray L S (T i)) :=
  map_sum (originalSourceCutNumeratorLinearMap L S p s) T Finset.univ

/-- Multiplying the finite annihilator applies the literal extra convolution. -/
theorem cutArrayNumerator_mul {G : Type*} [AddCommGroup G]
    (L : G →+ ℝ) (p q : AddMonoidAlgebra ℂ G) (s : ℝ) (u : G → ℂ) :
    cutArrayNumerator L (p * q).coeff s u =
      annihilatorArrayConvolution p.coeff (cutArrayNumerator L q.coeff s u) := by
  funext n
  exact annihilatorArrayConvolution_mul p q (arrayPositiveCut L s u) n

end
end MeyerGeneralProblem

namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The genuine lifted finite symbol is EXACTLY the actual positive original motif. -/
theorem originalPositiveIntegerCoefficients_symbol (scale x : ℝ)
    (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    annihilatorExponentialSymbol (originalScaledModuleFrequencyHom scale)
      (originalPositivePolynomialIntegerCoefficients q) x =
    finitePositiveExponentialSymbol
      (originalPositivePolynomialFrequency scale (originalPositivePolynomialCoordinates q))
      (originalPositivePolynomialCoefficient q) x := by
  classical
  change (q.coeff.mapDomain originalNativeIntegerEmbedding).sum
    (fun n c => c * combModulationCharacter (originalScaledModuleFrequencyHom scale n) x) = _
  rw [Finsupp.sum_mapDomain_index_inj originalNativeIntegerEmbedding.injective]
  change (∑ n ∈ q.coeff.support, q.coeff n *
    combModulationCharacter (originalScaledModuleFrequencyHom scale (originalNativeIntegerEmbedding n)) x) = _
  rw [← q.coeff.support.sum_coe_sort]
  rfl

/-- The WHOLE actual mixed integer annihilator vanishes on ALL full physical roots. -/
theorem originalScheduledPrefixIntegerCoefficients_vanishes (bound : ℕ → ℕ) (k : ℕ)
    (x : ℝ) (hx : x ∈ (originalScheduledPrefixFullRootCarrier bound k).carrier) :
    annihilatorExponentialSymbol
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
      (originalScheduledPrefixIntegerCoefficients bound k) x = 0 := by
  rw [originalScheduledPrefixIntegerCoefficients, originalPositiveIntegerCoefficients_symbol]
  exact originalScheduledPrefixPolynomial_vanishes bound k x hx

/-- Each actual source has its full mixed numerator, including every complement factor. -/
theorem originalScheduledNativeSource_fullPrefix_cutNumerator (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (r : productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ) :
    cutArrayNumerator
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
      (originalScheduledPrefixIntegerCoefficients bound k) 0
      (originalFourierArray
        (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
        (originalScheduledPrefixCone bound k) (originalScheduledNativeSource bound i.val r)) =
    (originalPositiveLaurentEmbedding (originalScheduledOtherBlocksPolynomial bound k i *
      originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
        (originalPhasedSlabPositivePolynomial (originalReflectedOrderSchedule bound i.val) r))).coeff := by
  change cutArrayNumerator _ (originalPositiveLaurentEmbedding (originalScheduledPrefixPolynomial bound k)).coeff 0 _ = _
  rw [originalScheduledPrefixPolynomial_block_complement bound k i, mul_comm
    (originalScheduledBlockPositivePolynomial bound k i), map_mul, cutArrayNumerator_mul,
    originalScheduledNativeSource_cutNumerator]
  funext n
  rw [annihilatorArrayConvolution_finite, ← map_mul]

/-- Every full source sum has its exact ALL-block whole mixed numerator. -/
theorem originalScheduledNativeSource_sum_cutNumerator (bound : ℕ → ℕ) (k : ℕ)
    (r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ) :
    cutArrayNumerator
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
      (originalScheduledPrefixIntegerCoefficients bound k) 0
      (originalFourierArray
        (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
        (originalScheduledPrefixCone bound k) (∑ i : Fin k, originalScheduledNativeSource bound i.val (r i))) =
    (originalPositiveLaurentEmbedding (∑ i : Fin k, originalScheduledOtherBlocksPolynomial bound k i *
      originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
        (originalPhasedSlabPositivePolynomial (originalReflectedOrderSchedule bound i.val) (r i)))).coeff := by
  classical
  rw [originalSourceCutNumerator_sum]
  simp only [originalScheduledNativeSource_fullPrefix_cutNumerator, map_sum, AddMonoidAlgebra.coeff_sum]
  funext n
  simp only [Finset.sum_apply, Finsupp.finsetSum_apply]

/-- The recovered WHOLE root component has every ORIGINAL module coefficient,
now read on the entire common cone without changing its carrier-supported record. -/
theorem originalScheduledPrefixRootSource_originalFourierArray (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    originalFourierArray
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
      (originalScheduledPrefixCone bound k) (originalScheduledPrefixRootSource bound k N T hF) =
      originalScheduledPrefixFourierArray bound k T := by
  funext z
  unfold originalFourierArray
  rw [originalScheduledPrefixRootSource_fourier]
  rw [← extendedAtomicCoefficient_two_carriers (originalScheduledPrefixCarrier bound k)
    (originalScheduledPrefixCone bound k) _
    (hasLocallyAtomicAction_atomicOnCarrier _ _
      (originalScheduledPrefixModuleSpectralRecord_mem_strongExponent bound k N T hF).1)
    (originalScheduledPrefixModuleSpectralRecord_atomicOnCone bound k N T hF)]
  exact originalScheduledPrefixModuleSpectralRecord_coefficient bound k N T hF z

end
end MeyerGeneralProblem.StrongParity
