module

public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalFractionCancellation

@[expose] public section

/-! Actual complete original character differences before other-block cancellation.
The numerator and common-complement denominator are literal native coefficients.
Mixed invariance follows internally from EVERY complete original strong pair. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The literal numerator of an actual selected native character difference. -/
def originalScheduledBlockDifferenceNumerator (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) (R : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g) R *
      originalScheduledBlockPositivePolynomial bound k i -
    R * originalScheduledCharacterBlockPolynomial bound k i g

/-- The actual selected block and its translate retain the exact whole complementary product. -/
def originalScheduledBlockDifferenceDenominator (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  originalScheduledBlockPositivePolynomial bound k i *
    originalScheduledCharacterBlockPolynomial bound k i g * originalScheduledOtherBlocksPolynomial bound k i

/-- Every actual common-complement difference denominator is internally nonzero. -/
theorem originalScheduledBlockDifferenceDenominator_ne_zero (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledBlockDifferenceDenominator bound k i g ≠ 0 := by
  unfold originalScheduledBlockDifferenceDenominator
  rw [← originalScheduledCharacterBlockPolynomial_one]
  exact mul_ne_zero (mul_ne_zero (originalScheduledCharacterBlockPolynomial_ne_zero bound k i _)
    (originalScheduledCharacterBlockPolynomial_ne_zero bound k i g))
    (originalScheduledOtherBlocksPolynomial_ne_zero bound k i)

/-- The genuine actual difference equals its literal common-complement polynomial fraction. -/
theorem originalScheduledBlockDifferenceFraction_normalize (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) (R : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    let χ := originalScheduledPrimeCharacter bound i.val g
    let P := originalScheduledPrefixPolynomial bound k
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalScheduledBlockDifferenceNumerator bound k i g R) /
        f (originalScheduledBlockDifferenceDenominator bound k i g) =
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ P) - f R / f P := by
  dsimp only
  rw [originalScheduledPrefixPolynomial_character_factorization, originalScheduledPrefixPolynomial_block_complement]
  apply originalPositiveFractionDifference_normalize
  · rw [← originalScheduledCharacterBlockPolynomial_one]
    exact originalScheduledCharacterBlockPolynomial_ne_zero bound k i _
  · exact originalScheduledCharacterBlockPolynomial_ne_zero bound k i g
  · exact originalScheduledOtherBlocksPolynomial_ne_zero bound k i

/-- Any other actual character twists the literal difference to exactly its mixed fraction difference. -/
theorem originalScheduledBlockDifferenceFraction_other_normalize (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) (R : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    let χ := originalScheduledPrimeCharacter bound i.val g
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let P := originalScheduledPrefixPolynomial bound k
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist ψ (originalScheduledBlockDifferenceNumerator bound k i g R)) /
        f (originalPositiveCharacterTwist ψ (originalScheduledBlockDifferenceDenominator bound k i g)) =
      f (originalPositiveCharacterTwist (χ * ψ) R) / f (originalPositiveCharacterTwist (χ * ψ) P) -
        f (originalPositiveCharacterTwist ψ R) / f (originalPositiveCharacterTwist ψ P) := by
  dsimp only
  let χ := originalScheduledPrimeCharacter bound i.val g
  let ψ := originalScheduledPrimeCharacter bound j.val h
  have hQi := originalScheduledPositiveBlock_other_character_invariant bound k j i hij.symm h
  have hQg := originalScheduledPositiveCharacterBlock_other_invariant bound k j i hij.symm h g
  have hP : originalPositiveCharacterTwist ψ (originalScheduledPrefixPolynomial bound k) =
      originalScheduledBlockPositivePolynomial bound k i *
        originalPositiveCharacterTwist ψ (originalScheduledOtherBlocksPolynomial bound k i) := by
    rw [originalScheduledPrefixPolynomial_block_complement bound k i, map_mul, hQi]
  have hχψP : originalPositiveCharacterTwist (χ * ψ) (originalScheduledPrefixPolynomial bound k) =
      originalScheduledCharacterBlockPolynomial bound k i g *
        originalPositiveCharacterTwist ψ (originalScheduledOtherBlocksPolynomial bound k i) := by
    rw [mul_comm χ ψ, originalPositiveCharacterTwist_mul,
      originalScheduledPrefixPolynomial_character_factorization, map_mul, hQg]
  have hψχR : originalPositiveCharacterTwist ψ (originalPositiveCharacterTwist χ R) =
      originalPositiveCharacterTwist (χ * ψ) R := by
    rw [← originalPositiveCharacterTwist_mul, mul_comm ψ χ]
  have hA : originalPositiveCharacterTwist ψ (originalScheduledBlockDifferenceNumerator bound k i g R) =
      originalPositiveCharacterTwist (χ * ψ) R * originalScheduledBlockPositivePolynomial bound k i -
        originalPositiveCharacterTwist ψ R * originalScheduledCharacterBlockPolynomial bound k i g := by
    simp only [originalScheduledBlockDifferenceNumerator, map_mul, map_sub]
    rw [hψχR, hQi, hQg]
  have hD : originalPositiveCharacterTwist ψ (originalScheduledBlockDifferenceDenominator bound k i g) =
      originalScheduledBlockPositivePolynomial bound k i * originalScheduledCharacterBlockPolynomial bound k i g *
        originalPositiveCharacterTwist ψ (originalScheduledOtherBlocksPolynomial bound k i) := by
    simp only [originalScheduledBlockDifferenceDenominator, map_mul]
    rw [hQi, hQg]
  rw [hA, hD, hP, hχψP]
  apply originalPositiveFractionDifference_normalize
  · rw [← originalScheduledCharacterBlockPolynomial_one]
    exact originalScheduledCharacterBlockPolynomial_ne_zero bound k i _
  · exact originalScheduledCharacterBlockPolynomial_ne_zero bound k i g
  · exact originalPositiveCharacterTwist_ne_zero ψ _ (originalScheduledOtherBlocksPolynomial_ne_zero bound k i)

/-- The actual mixed polynomial equation makes a selected difference invariant under every other actual character. -/
theorem originalScheduledBlockDifferenceFraction_invariant_of_mixed (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) (R : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hmix : originalPositiveMixedNumerator (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledPrimeCharacter bound j.val h) (originalScheduledPrefixPolynomial bound k) R = 0) :
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist ψ (originalScheduledBlockDifferenceNumerator bound k i g R)) /
        f (originalPositiveCharacterTwist ψ (originalScheduledBlockDifferenceDenominator bound k i g)) =
      f (originalScheduledBlockDifferenceNumerator bound k i g R) /
        f (originalScheduledBlockDifferenceDenominator bound k i g) := by
  dsimp only
  rw [originalScheduledBlockDifferenceFraction_other_normalize bound k i j hij g h R,
    originalScheduledBlockDifferenceFraction_normalize]
  have hm := originalPositiveMixedFractions_eq_zero _ _ _ R
    (originalScheduledPrefixPolynomial_ne_zero bound k) hmix
  dsimp only at hm
  linear_combination hm

/-- EVERY complete original positive cut supplies the required difference invariance internally. -/
theorem originalScheduledPrefixBlockDifferenceFraction_other_invariant (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    let R := originalScheduledPrefixPositiveNumerator bound k T hT
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist ψ (originalScheduledBlockDifferenceNumerator bound k i g R)) /
        f (originalPositiveCharacterTwist ψ (originalScheduledBlockDifferenceDenominator bound k i g)) =
      f (originalScheduledBlockDifferenceNumerator bound k i g R) /
        f (originalScheduledBlockDifferenceDenominator bound k i g) :=
  originalScheduledBlockDifferenceFraction_invariant_of_mixed bound k i j hij g h _
    (originalScheduledPrefixPositiveNumerator_mixed_identity bound k T hT i j hij g h)

/-- The strict original negative cut supplies the same difference invariance with its exact sign. -/
theorem originalScheduledPrefixNegativeBlockDifferenceFraction_other_invariant (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    let R := -originalScheduledPrefixPositiveNumerator bound k T hT
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist ψ (originalScheduledBlockDifferenceNumerator bound k i g R)) /
        f (originalPositiveCharacterTwist ψ (originalScheduledBlockDifferenceDenominator bound k i g)) =
      f (originalScheduledBlockDifferenceNumerator bound k i g R) /
        f (originalScheduledBlockDifferenceDenominator bound k i g) :=
  originalScheduledBlockDifferenceFraction_invariant_of_mixed bound k i j hij g h _
    (originalScheduledPrefixNegativePositiveNumerator_mixed_identity bound k T hT i j hij g h)

end
end MeyerGeneralProblem.StrongParity
