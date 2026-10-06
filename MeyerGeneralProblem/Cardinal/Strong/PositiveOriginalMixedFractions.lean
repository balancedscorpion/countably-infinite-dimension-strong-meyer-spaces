module

public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalNumerator
public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalCharacterTwists
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-! The COMPLETE original finite-prefix strong pair obeys its actual mixed
rational equation in the genuine positive polynomial fraction field. The exact
embedding pulls back the retained fraction-free identity before division. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual four-denominator mixed numerator in the positive original coefficient algebra. -/
def originalPositiveMixedNumerator (χ ψ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (p R : AddMonoidAlgebra ℂ (ℕ × ℕ)) : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  (p * originalPositiveCharacterTwist χ p * originalPositiveCharacterTwist ψ p) *
      originalPositiveCharacterTwist (χ * ψ) R -
    (p * originalPositiveCharacterTwist ψ p * originalPositiveCharacterTwist (χ * ψ) p) *
      originalPositiveCharacterTwist χ R -
    (p * originalPositiveCharacterTwist χ p * originalPositiveCharacterTwist (χ * ψ) p) *
      originalPositiveCharacterTwist ψ R +
    (originalPositiveCharacterTwist χ p * originalPositiveCharacterTwist ψ p *
      originalPositiveCharacterTwist (χ * ψ) p) * R

/-- The positive mixed numerator embeds to the exact retained whole Laurent mixed numerator. -/
theorem originalPositiveMixedNumerator_laurent (χ ψ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (p R : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    originalPositiveLaurentEmbedding (originalPositiveMixedNumerator χ ψ p R) =
      originalLaurentMixedNumerator χ ψ (originalPositiveLaurentEmbedding p)
        (originalPositiveLaurentEmbedding R) := by
  simp only [originalPositiveMixedNumerator, originalLaurentMixedNumerator, map_add, map_sub,
    map_mul, originalPositiveCharacterTwist_laurent]

/-- EVERY complete actual original strong pair supplies its positive mixed polynomial equation internally. -/
theorem originalScheduledPrefixPositiveNumerator_mixed_identity (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    originalPositiveMixedNumerator (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledPrimeCharacter bound j.val h) (originalScheduledPrefixPolynomial bound k)
      (originalScheduledPrefixPositiveNumerator bound k T hT) = 0 := by
  apply originalPositiveLaurentEmbedding_injective
  rw [originalPositiveMixedNumerator_laurent, map_zero, originalScheduledPrefixPolynomial_laurent,
    originalScheduledPrefixPositiveNumerator_laurent]
  exact originalScheduledPrefixLaurentNumerator_mixed_character_identity bound k T hT i j hij g h

/-- The strict original negative cut supplies the same positive algebra equation with its exact sign. -/
theorem originalScheduledPrefixNegativePositiveNumerator_mixed_identity (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    originalPositiveMixedNumerator (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledPrimeCharacter bound j.val h) (originalScheduledPrefixPolynomial bound k)
      (-originalScheduledPrefixPositiveNumerator bound k T hT) = 0 := by
  apply originalPositiveLaurentEmbedding_injective
  rw [originalPositiveMixedNumerator_laurent, map_zero, originalScheduledPrefixPolynomial_laurent,
    map_neg, originalScheduledPrefixPositiveNumerator_laurent]
  exact originalScheduledPrefixNegativeLaurentNumerator_mixed_character_identity bound k T hT i j hij g h

/-- All four genuine positive denominators are nonzero under any unit-character pair. -/
theorem originalPositiveMixedDenominator_ne_zero (χ ψ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : p ≠ 0) :
    p * originalPositiveCharacterTwist χ p * originalPositiveCharacterTwist ψ p *
      originalPositiveCharacterTwist (χ * ψ) p ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero hp (originalPositiveCharacterTwist_ne_zero χ p hp))
    (originalPositiveCharacterTwist_ne_zero ψ p hp))
    (originalPositiveCharacterTwist_ne_zero (χ * ψ) p hp)

/-- A genuine positive mixed polynomial identity implies its fraction-field equation. -/
theorem originalPositiveMixedFractions_eq_zero (χ ψ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (p R : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : p ≠ 0)
    (hmix : originalPositiveMixedNumerator χ ψ p R = 0) :
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist (χ * ψ) R) / f (originalPositiveCharacterTwist (χ * ψ) p) -
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ p) -
      f (originalPositiveCharacterTwist ψ R) / f (originalPositiveCharacterTwist ψ p) + f R / f p = 0 := by
  let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  have hp0 : f p ≠ 0 := (map_ne_zero_iff f hinj).mpr hp
  have hχ : f (originalPositiveCharacterTwist χ p) ≠ 0 :=
    (map_ne_zero_iff f hinj).mpr (originalPositiveCharacterTwist_ne_zero χ p hp)
  have hψ : f (originalPositiveCharacterTwist ψ p) ≠ 0 :=
    (map_ne_zero_iff f hinj).mpr (originalPositiveCharacterTwist_ne_zero ψ p hp)
  have hχψ : f (originalPositiveCharacterTwist (χ * ψ) p) ≠ 0 :=
    (map_ne_zero_iff f hinj).mpr (originalPositiveCharacterTwist_ne_zero (χ * ψ) p hp)
  have hm := congrArg f hmix
  simp only [originalPositiveMixedNumerator, map_add, map_sub, map_mul, map_zero] at hm
  change f (originalPositiveCharacterTwist (χ * ψ) R) / f (originalPositiveCharacterTwist (χ * ψ) p) -
    f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ p) -
    f (originalPositiveCharacterTwist ψ R) / f (originalPositiveCharacterTwist ψ p) + f R / f p = 0
  field_simp [hp0, hχ, hψ, hχψ]
  linear_combination hm

/-- The actual complete original positive cut obeys its polynomial fraction-field mixed identity,
with all numerator, denominator and character inputs derived internally. -/
theorem originalScheduledPrefixPositiveMixedFractions_eq_zero (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    let χ := originalScheduledPrimeCharacter bound i.val g
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let p := originalScheduledPrefixPolynomial bound k
    let R := originalScheduledPrefixPositiveNumerator bound k T hT
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist (χ * ψ) R) / f (originalPositiveCharacterTwist (χ * ψ) p) -
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ p) -
      f (originalPositiveCharacterTwist ψ R) / f (originalPositiveCharacterTwist ψ p) + f R / f p = 0 :=
  originalPositiveMixedFractions_eq_zero _ _ _ _ (originalScheduledPrefixPolynomial_ne_zero bound k)
    (originalScheduledPrefixPositiveNumerator_mixed_identity bound k T hT i j hij g h)

/-- The actual strict negative cut has the same genuine polynomial fraction identity with its sign. -/
theorem originalScheduledPrefixNegativePositiveMixedFractions_eq_zero (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    let χ := originalScheduledPrimeCharacter bound i.val g
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let p := originalScheduledPrefixPolynomial bound k
    let R := -originalScheduledPrefixPositiveNumerator bound k T hT
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist (χ * ψ) R) / f (originalPositiveCharacterTwist (χ * ψ) p) -
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ p) -
      f (originalPositiveCharacterTwist ψ R) / f (originalPositiveCharacterTwist ψ p) + f R / f p = 0 :=
  originalPositiveMixedFractions_eq_zero _ _ _ _ (originalScheduledPrefixPolynomial_ne_zero bound k)
    (originalScheduledPrefixNegativePositiveNumerator_mixed_identity bound k T hT i j hij g h)

end
end MeyerGeneralProblem.StrongParity
