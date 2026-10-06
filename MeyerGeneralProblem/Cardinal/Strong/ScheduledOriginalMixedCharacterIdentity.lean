module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalSparseCharacters
public import MeyerGeneralProblem.Cardinal.Strong.LaurentMixedNumeratorIdentity

@[expose] public section

/-! The actual scheduled mixed Laurent polynomial and the actual original cut
numerator obey the mixed finite-character identity. EVERY structural input is
proved from complete ORIGINAL strong membership and the literal carrier. The
quarter phase and all coefficient collisions remain those of the original product. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Actual common-integer Laurent polynomial, after ALL original coefficient collisions. -/
def originalScheduledPrefixLaurentPolynomial (bound : ℕ → ℕ) (k : ℕ) :
    AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  AddMonoidAlgebra.ofCoeff (originalScheduledPrefixIntegerCoefficients bound k)

/-- Actual finite original numerator, containing BOTH cut formulas on ALL labels. -/
def originalScheduledPrefixLaurentNumerator (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  AddMonoidAlgebra.ofCoeff (originalScheduledPrefixNumerator bound k T hT)

/-- EVERY actual denominator coefficient is the retained ORIGINAL mixed coefficient. -/
theorem originalScheduledPrefixLaurentPolynomial_coefficient (bound : ℕ → ℕ) (k : ℕ) (z : ℤ × ℤ) :
    (originalScheduledPrefixLaurentPolynomial bound k).coeff z =
      originalScheduledPrefixIntegerCoefficients bound k z := rfl

/-- The actual denominator is internally nonzero, including the EMPTY prefix unit. -/
theorem originalScheduledPrefixLaurentPolynomial_ne_zero (bound : ℕ → ℕ) (k : ℕ) :
    originalScheduledPrefixLaurentPolynomial bound k ≠ 0 := by
  intro h
  apply originalScheduledPrefixIntegerCoefficients_ne_zero bound k
  exact congrArg AddMonoidAlgebra.coeff h

/-- The WHOLE positive numerator formula is original, with zero retained exactly once. -/
theorem originalScheduledPrefixLaurentNumerator_positive (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (z : ℤ × ℤ) :
    (originalScheduledPrefixLaurentNumerator bound k T hT).coeff z = annihilatorArrayConvolution
      (originalScheduledPrefixLaurentPolynomial bound k).coeff
      (arrayPositiveCut
        (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
        0 (originalScheduledPrefixFourierArray bound k T)) z := rfl

/-- The strict ORIGINAL negative cut supplies the same finite numerator with its exact sign. -/
theorem originalScheduledPrefixLaurentNumerator_negative (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (z : ℤ × ℤ) :
    (-originalScheduledPrefixLaurentNumerator bound k T hT).coeff z = annihilatorArrayConvolution
      (originalScheduledPrefixLaurentPolynomial bound k).coeff
      (arrayNegativeCut
        (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
        0 (originalScheduledPrefixFourierArray bound k T)) z := by
  change -originalScheduledPrefixNumerator bound k T hT z = _
  rw [originalScheduledPrefixNumerator_negative, neg_neg]
  rfl

/-- EVERY actual complete original strong pair satisfies the fraction-free mixed
character identity, without a sparse/rational/character/polynomial certificate. -/
theorem originalScheduledPrefixLaurentNumerator_mixed_character_identity (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    originalLaurentMixedNumerator (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledPrimeCharacter bound j.val h)
      (originalScheduledPrefixLaurentPolynomial bound k)
      (originalScheduledPrefixLaurentNumerator bound k T hT) = 0 := by
  exact originalLaurentMixedNumerator_eq_zero _ _ _ _ _
    (originalScheduledPrefixLaurentNumerator_positive bound k T hT)
    (originalScheduledPrefixPositiveCut_mixed_character_zero bound k T hT i j hij g h)

/-- The same exact mixed identity holds for the strict original negative numerator. -/
theorem originalScheduledPrefixNegativeLaurentNumerator_mixed_character_identity (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    originalLaurentMixedNumerator (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledPrimeCharacter bound j.val h)
      (originalScheduledPrefixLaurentPolynomial bound k)
      (-originalScheduledPrefixLaurentNumerator bound k T hT) = 0 := by
  exact originalLaurentMixedNumerator_eq_zero _ _ _ _ _
    (originalScheduledPrefixLaurentNumerator_negative bound k T hT)
    (originalScheduledPrefixNegativeCut_mixed_character_zero bound k T hT i j hij g h)

/-- The actual four-factor clearing polynomial is truly nonzero for EVERY torus action. -/
theorem originalScheduledPrefixMixedDenominator_ne_zero (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    originalScheduledPrefixLaurentPolynomial bound k *
      originalLaurentCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
        (originalScheduledPrefixLaurentPolynomial bound k) *
      originalLaurentCharacterTwist (originalScheduledPrimeCharacter bound j.val h)
        (originalScheduledPrefixLaurentPolynomial bound k) *
      originalLaurentCharacterTwist
        (originalScheduledPrimeCharacter bound i.val g * originalScheduledPrimeCharacter bound j.val h)
        (originalScheduledPrefixLaurentPolynomial bound k) ≠ 0 :=
  originalLaurentMixedDenominator_ne_zero _ _ _ (originalScheduledPrefixLaurentPolynomial_ne_zero bound k)

end
end MeyerGeneralProblem.StrongParity
