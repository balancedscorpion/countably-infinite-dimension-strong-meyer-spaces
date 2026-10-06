module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalChartBlocks

@[expose] public section

/-! Actual complete original character differences before other-block cancellation.
The numerator and common-complement denominator are literal native coefficients.
Mixed invariance follows internally from EVERY complete original strong pair. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The literal numerator of an actual selected native character difference. -/
def originalScheduledChartBlockDifferenceNumerator (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) (R : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g) R *
      originalScheduledChartBlockPolynomial c bound k i -
    R * originalScheduledChartCharacterBlockPolynomial c bound k i g

/-- The actual selected block and its translate retain the exact whole complementary product. -/
def originalScheduledChartBlockDifferenceDenominator (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  originalScheduledChartBlockPolynomial c bound k i *
    originalScheduledChartCharacterBlockPolynomial c bound k i g * originalScheduledChartOtherBlocksPolynomial c bound k i

/-- Every actual common-complement difference denominator is internally nonzero. -/
theorem originalScheduledChartBlockDifferenceDenominator_ne_zero (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledChartBlockDifferenceDenominator c bound k i g ≠ 0 := by
  unfold originalScheduledChartBlockDifferenceDenominator
  rw [← originalScheduledChartCharacterBlockPolynomial_one c]
  exact mul_ne_zero (mul_ne_zero (originalScheduledChartCharacterBlockPolynomial_ne_zero c bound k i _)
    (originalScheduledChartCharacterBlockPolynomial_ne_zero c bound k i g))
    (originalScheduledChartOtherBlocksPolynomial_ne_zero c bound k i)

/-- The genuine actual difference equals its literal common-complement polynomial fraction. -/
theorem originalScheduledChartBlockDifferenceFraction_normalize (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) (R : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    let χ := originalScheduledPrimeCharacter bound i.val g
    let P := originalScheduledPrefixChartPolynomial c bound k
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalScheduledChartBlockDifferenceNumerator c bound k i g R) /
        f (originalScheduledChartBlockDifferenceDenominator c bound k i g) =
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ P) - f R / f P := by
  dsimp only
  rw [originalScheduledPrefixChartPolynomial_character_factorization c, originalScheduledPrefixChartPolynomial_block_complement c]
  apply originalPositiveFractionDifference_normalize
  · rw [← originalScheduledChartCharacterBlockPolynomial_one c]
    exact originalScheduledChartCharacterBlockPolynomial_ne_zero c bound k i _
  · exact originalScheduledChartCharacterBlockPolynomial_ne_zero c bound k i g
  · exact originalScheduledChartOtherBlocksPolynomial_ne_zero c bound k i

/-- Any other actual character twists the literal difference to exactly its mixed fraction difference. -/
theorem originalScheduledChartBlockDifferenceFraction_other_normalize (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) (R : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    let χ := originalScheduledPrimeCharacter bound i.val g
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let P := originalScheduledPrefixChartPolynomial c bound k
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist ψ (originalScheduledChartBlockDifferenceNumerator c bound k i g R)) /
        f (originalPositiveCharacterTwist ψ (originalScheduledChartBlockDifferenceDenominator c bound k i g)) =
      f (originalPositiveCharacterTwist (χ * ψ) R) / f (originalPositiveCharacterTwist (χ * ψ) P) -
        f (originalPositiveCharacterTwist ψ R) / f (originalPositiveCharacterTwist ψ P) := by
  dsimp only
  let χ := originalScheduledPrimeCharacter bound i.val g
  let ψ := originalScheduledPrimeCharacter bound j.val h
  have hQi := originalScheduledChartBlock_other_character_invariant c bound k j i hij.symm h
  have hQg := originalScheduledChartCharacterBlock_other_invariant c bound k j i hij.symm h g
  have hP : originalPositiveCharacterTwist ψ (originalScheduledPrefixChartPolynomial c bound k) =
      originalScheduledChartBlockPolynomial c bound k i *
        originalPositiveCharacterTwist ψ (originalScheduledChartOtherBlocksPolynomial c bound k i) := by
    rw [originalScheduledPrefixChartPolynomial_block_complement c bound k i, map_mul, hQi]
  have hχψP : originalPositiveCharacterTwist (χ * ψ) (originalScheduledPrefixChartPolynomial c bound k) =
      originalScheduledChartCharacterBlockPolynomial c bound k i g *
        originalPositiveCharacterTwist ψ (originalScheduledChartOtherBlocksPolynomial c bound k i) := by
    rw [mul_comm χ ψ, originalPositiveCharacterTwist_mul,
      originalScheduledPrefixChartPolynomial_character_factorization c, map_mul, hQg]
  have hψχR : originalPositiveCharacterTwist ψ (originalPositiveCharacterTwist χ R) =
      originalPositiveCharacterTwist (χ * ψ) R := by
    rw [← originalPositiveCharacterTwist_mul, mul_comm ψ χ]
  have hA : originalPositiveCharacterTwist ψ (originalScheduledChartBlockDifferenceNumerator c bound k i g R) =
      originalPositiveCharacterTwist (χ * ψ) R * originalScheduledChartBlockPolynomial c bound k i -
        originalPositiveCharacterTwist ψ R * originalScheduledChartCharacterBlockPolynomial c bound k i g := by
    simp only [originalScheduledChartBlockDifferenceNumerator, map_mul, map_sub]
    rw [hψχR, hQi, hQg]
  have hD : originalPositiveCharacterTwist ψ (originalScheduledChartBlockDifferenceDenominator c bound k i g) =
      originalScheduledChartBlockPolynomial c bound k i * originalScheduledChartCharacterBlockPolynomial c bound k i g *
        originalPositiveCharacterTwist ψ (originalScheduledChartOtherBlocksPolynomial c bound k i) := by
    simp only [originalScheduledChartBlockDifferenceDenominator, map_mul]
    rw [hQi, hQg]
  rw [hA, hD, hP, hχψP]
  apply originalPositiveFractionDifference_normalize
  · rw [← originalScheduledChartCharacterBlockPolynomial_one c]
    exact originalScheduledChartCharacterBlockPolynomial_ne_zero c bound k i _
  · exact originalScheduledChartCharacterBlockPolynomial_ne_zero c bound k i g
  · exact originalPositiveCharacterTwist_ne_zero ψ _ (originalScheduledChartOtherBlocksPolynomial_ne_zero c bound k i)

/-- The actual mixed polynomial equation makes a selected difference invariant under every other actual character. -/
theorem originalScheduledChartBlockDifferenceFraction_invariant_of_mixed (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) (R : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hmix : originalPositiveMixedNumerator (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledPrimeCharacter bound j.val h) (originalScheduledPrefixChartPolynomial c bound k) R = 0) :
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist ψ (originalScheduledChartBlockDifferenceNumerator c bound k i g R)) /
        f (originalPositiveCharacterTwist ψ (originalScheduledChartBlockDifferenceDenominator c bound k i g)) =
      f (originalScheduledChartBlockDifferenceNumerator c bound k i g R) /
        f (originalScheduledChartBlockDifferenceDenominator c bound k i g) := by
  dsimp only
  rw [originalScheduledChartBlockDifferenceFraction_other_normalize c bound k i j hij g h R,
    originalScheduledChartBlockDifferenceFraction_normalize c]
  have hm := originalPositiveMixedFractions_eq_zero _ _ _ R
    (originalScheduledPrefixChartPolynomial_ne_zero c bound k) hmix
  dsimp only at hm
  linear_combination hm

/-- EVERY complete original positive cut supplies the required difference invariance internally. -/
theorem originalScheduledPrefixChartBlockDifferenceFraction_other_invariant (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    let R := originalScheduledPrefixChartNumerator c bound k T hT
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist ψ (originalScheduledChartBlockDifferenceNumerator c bound k i g R)) /
        f (originalPositiveCharacterTwist ψ (originalScheduledChartBlockDifferenceDenominator c bound k i g)) =
      f (originalScheduledChartBlockDifferenceNumerator c bound k i g R) /
        f (originalScheduledChartBlockDifferenceDenominator c bound k i g) :=
  originalScheduledChartBlockDifferenceFraction_invariant_of_mixed c bound k i j hij g h _
    (originalScheduledPrefixChartNumerator_mixed_identity c bound k T hT i j hij g h)

/-- The strict original negative cut supplies the same difference invariance with its exact sign. -/
theorem originalScheduledPrefixNegativeChartBlockDifferenceFraction_other_invariant (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    let R := -originalScheduledPrefixChartNumerator c bound k T hT
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist ψ (originalScheduledChartBlockDifferenceNumerator c bound k i g R)) /
        f (originalPositiveCharacterTwist ψ (originalScheduledChartBlockDifferenceDenominator c bound k i g)) =
      f (originalScheduledChartBlockDifferenceNumerator c bound k i g R) /
        f (originalScheduledChartBlockDifferenceDenominator c bound k i g) :=
  originalScheduledChartBlockDifferenceFraction_invariant_of_mixed c bound k i j hij g h _
    (originalScheduledPrefixNegativeChartNumerator_mixed_identity c bound k T hT i j hij g h)

end
end MeyerGeneralProblem.StrongParity
