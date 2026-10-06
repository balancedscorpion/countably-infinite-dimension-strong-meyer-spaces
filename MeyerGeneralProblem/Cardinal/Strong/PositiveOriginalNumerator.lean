module

public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalLaurentEmbedding
public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalMixedCharacterIdentity

@[expose] public section

/-! Every complete original finite-prefix strong pair has a genuine positive
polynomial numerator. Its exact integer coefficients, full native box and missing
top corner are derived internally from the original pair, including both cuts. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual numerator reindexed at its original nonnegative native coordinates. -/
def originalScheduledPrefixPositiveNumerator (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  AddMonoidAlgebra.comapDomain originalNativeIntegerEmbedding
    originalNativeIntegerEmbedding.injective (originalScheduledPrefixLaurentNumerator bound k T hT)

/-- Every native positive coefficient is the literal original integer numerator coefficient. -/
theorem originalScheduledPrefixPositiveNumerator_coeff (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (n : ℕ × ℕ) :
    (originalScheduledPrefixPositiveNumerator bound k T hT).coeff n =
      originalScheduledPrefixNumerator bound k T hT (originalNativeIntegerEmbedding n) := rfl

/-- The positive native numerator retains the literal original positive-cut convolution. -/
theorem originalScheduledPrefixPositiveNumerator_positive (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (n : ℕ × ℕ) :
    (originalScheduledPrefixPositiveNumerator bound k T hT).coeff n =
      annihilatorArrayConvolution (originalScheduledPrefixIntegerCoefficients bound k)
        (arrayPositiveCut
          (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
          0 (originalScheduledPrefixFourierArray bound k T)) (originalNativeIntegerEmbedding n) := by
  rw [originalScheduledPrefixPositiveNumerator_coeff, originalScheduledPrefixNumerator_positive]

/-- The strict original negative cut gives the same native numerator with its exact sign. -/
theorem originalScheduledPrefixPositiveNumerator_negative (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (n : ℕ × ℕ) :
    (originalScheduledPrefixPositiveNumerator bound k T hT).coeff n =
      -annihilatorArrayConvolution (originalScheduledPrefixIntegerCoefficients bound k)
        (arrayNegativeCut
          (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
          0 (originalScheduledPrefixFourierArray bound k T)) (originalNativeIntegerEmbedding n) := by
  rw [originalScheduledPrefixPositiveNumerator_coeff, originalScheduledPrefixNumerator_negative]

/-- ALL original numerator support is internally known to be in the positive coordinate image. -/
theorem originalScheduledPrefixNumerator_support_positive_image (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ↑(originalScheduledPrefixLaurentNumerator bound k T hT).coeff.support ⊆
      Set.range originalNativeIntegerEmbedding := by
  intro n hn
  have hb := originalScheduledPrefixNumerator_support_box bound k T hT hn
  refine ⟨(n.1.toNat, n.2.toNat), ?_⟩
  apply Prod.ext
  · exact Int.toNat_of_nonneg hb.1
  · exact Int.toNat_of_nonneg hb.2.2.1

/-- The reindexing round trip recovers EVERY original integer coefficient, including exterior rows. -/
theorem originalScheduledPrefixPositiveNumerator_laurent (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    originalPositiveLaurentEmbedding (originalScheduledPrefixPositiveNumerator bound k T hT) =
      originalScheduledPrefixLaurentNumerator bound k T hT :=
  AddMonoidAlgebra.mapDomain_comapDomain
    (originalScheduledPrefixNumerator_support_positive_image bound k T hT)
    originalNativeIntegerEmbedding.injective

/-- The positive numerator retains the COMPLETE original native box and missing top corner. -/
theorem originalScheduledPrefixPositiveNumerator_support_box (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) {n : ℕ × ℕ}
    (hn : n ∈ (originalScheduledPrefixPositiveNumerator bound k T hT).coeff.support) :
    n.1 ≤ originalScheduledPrefixPolynomialDegree bound k ∧
      n.2 ≤ originalScheduledPrefixPolynomialDegree bound k ∧
      n ≠ (originalScheduledPrefixPolynomialDegree bound k, originalScheduledPrefixPolynomialDegree bound k) := by
  have hz : originalNativeIntegerEmbedding n ∈ (originalScheduledPrefixNumerator bound k T hT).support := by
    simpa only [Finsupp.mem_support_iff, originalScheduledPrefixPositiveNumerator_coeff] using hn
  have hb := originalScheduledPrefixNumerator_support_box bound k T hT hz
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast (show (n.1 : ℤ) ≤ (originalScheduledPrefixPolynomialDegree bound k : ℤ) from hb.2.1)
  · exact_mod_cast (show (n.2 : ℤ) ≤ (originalScheduledPrefixPolynomialDegree bound k : ℤ) from hb.2.2.2.1)
  · intro he
    apply hb.2.2.2.2
    rw [he]
    rfl

/-- The actual empty-prefix positive numerator is zero, derived from the original complete pair. -/
theorem originalScheduledPrefixPositiveNumerator_empty (bound : ℕ → ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound 0)) :
    originalScheduledPrefixPositiveNumerator bound 0 T hT = 0 := by
  apply originalPositiveLaurentEmbedding_injective
  rw [originalScheduledPrefixPositiveNumerator_laurent, map_zero]
  change AddMonoidAlgebra.ofCoeff (originalScheduledPrefixNumerator bound 0 T hT) = 0
  rw [originalScheduledPrefixNumerator_empty]
  rfl

/-- The actual positive denominator embeds to the literal original Laurent denominator. -/
theorem originalScheduledPrefixPolynomial_laurent (bound : ℕ → ℕ) (k : ℕ) :
    originalPositiveLaurentEmbedding (originalScheduledPrefixPolynomial bound k) =
      originalScheduledPrefixLaurentPolynomial bound k := rfl

/-- Equality of actual positive numerators determines the WHOLE original integer module array. -/
theorem originalScheduledPrefixPositiveNumerator_determines_original_array (bound : ℕ → ℕ) (k : ℕ)
    (T U : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (hU : U ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (heq : originalScheduledPrefixPositiveNumerator bound k T hT =
      originalScheduledPrefixPositiveNumerator bound k U hU) :
    originalScheduledPrefixFourierArray bound k T = originalScheduledPrefixFourierArray bound k U := by
  have hl := congrArg originalPositiveLaurentEmbedding heq
  rw [originalScheduledPrefixPositiveNumerator_laurent, originalScheduledPrefixPositiveNumerator_laurent] at hl
  exact originalScheduledPrefixNumerator_determines_original_array bound k T U hT hU
    (congrArg AddMonoidAlgebra.coeff hl)

end
end MeyerGeneralProblem.StrongParity
