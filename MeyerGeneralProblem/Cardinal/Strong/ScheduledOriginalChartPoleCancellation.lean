module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalChartDifferences

@[expose] public section

/-! Actual complete original character differences cancel ALL other block factors
on EVERY fixed native chart. BOTH original root-component cuts are included.
The retained cone/root companion is not classified by this cancellation. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Every other actual whole block divides the literal complementary product. -/
theorem originalScheduledChartOtherBlock_dvd_complement (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) :
    originalScheduledChartBlockPolynomial c bound k j ∣ originalScheduledChartOtherBlocksPolynomial c bound k i := by
  classical
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)

/-- Every other actual whole block divides the genuine uncanceled difference denominator. -/
theorem originalScheduledChartOtherBlock_dvd_difference_denominator (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledChartBlockPolynomial c bound k j ∣ originalScheduledChartBlockDifferenceDenominator c bound k i g :=
  (originalScheduledChartOtherBlock_dvd_complement c bound k i j hij).mul_left _

/-- A nonidentity actual other character makes its whole block relatively prime to
the twisted complete difference denominator, with all original factors retained. -/
theorem originalScheduledChartOtherBlock_isRelPrime_twisted_difference_denominator
    (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i j : Fin k) (hij : i ≠ j)
    (g : OriginalScheduledPrimeTorus bound i.val) (h : OriginalScheduledPrimeTorus bound j.val)
    (hh : h ≠ originalScheduledPrimeTorusIdentity bound j.val) :
    IsRelPrime (originalScheduledChartBlockPolynomial c bound k j)
      (originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val h)
        (originalScheduledChartBlockDifferenceDenominator c bound k i g)) := by
  classical
  have hQi := originalScheduledChartBlockPolynomial_other_isRelPrime c bound k j i hij.symm
  have hQg : IsRelPrime (originalScheduledChartBlockPolynomial c bound k j)
      (originalScheduledChartCharacterBlockPolynomial c bound k i g) := by
    rw [← originalScheduledChartCharacterBlockPolynomial_one c]
    exact originalScheduledChartCharacterBlocks_other_block_isRelPrime c bound k j i hij.symm _ g
  have hE : IsRelPrime (originalScheduledChartBlockPolynomial c bound k j)
      (originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val h)
        (originalScheduledChartOtherBlocksPolynomial c bound k i)) := by
    unfold originalScheduledChartOtherBlocksPolynomial
    rw [map_prod]
    apply IsRelPrime.prod_right
    intro t _
    by_cases htj : t = j
    · subst t
      rw [originalScheduledChartBlock_character_twist c, ← originalScheduledChartCharacterBlockPolynomial_one c]
      exact originalScheduledChartCharacterBlocks_same_block_isRelPrime c bound k j _ h hh.symm
    · rw [originalScheduledChartBlock_other_character_invariant c bound k j t (Ne.symm htj) h]
      exact originalScheduledChartBlockPolynomial_other_isRelPrime c bound k j t (Ne.symm htj)
  simp only [originalScheduledChartBlockDifferenceDenominator, map_mul,
    originalScheduledChartBlock_other_character_invariant c bound k j i hij.symm h,
    originalScheduledChartCharacterBlock_other_invariant c bound k j i hij.symm h g]
  exact (hQi.mul_right hQg).mul_right hE

/-- EVERY actual complete original positive-cut difference numerator is divisible by each other whole block. -/
theorem originalScheduledPrefixChartOtherBlock_dvd_difference_numerator (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledChartBlockPolynomial c bound k j ∣
      originalScheduledChartBlockDifferenceNumerator c bound k i g (originalScheduledPrefixChartNumerator c bound k T hT) := by
  let h := originalScheduledNonidentityPrimeTorus bound j.val
  exact originalPositiveInvariantFraction_dvd_numerator (originalScheduledPrimeCharacter bound j.val h) _ _ _
    (originalScheduledChartBlockDifferenceDenominator_ne_zero c bound k i g)
    (originalScheduledChartOtherBlock_dvd_difference_denominator c bound k i j hij g)
    (originalScheduledChartOtherBlock_isRelPrime_twisted_difference_denominator c bound k i j hij g h
      (originalScheduledNonidentityPrimeTorus_ne_identity bound j.val))
    (originalScheduledPrefixChartBlockDifferenceFraction_other_invariant c bound k T hT i j hij g h)

/-- The strict original negative-cut difference has the same internally derived whole-block divisibility. -/
theorem originalScheduledPrefixNegativeChartOtherBlock_dvd_difference_numerator (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledChartBlockPolynomial c bound k j ∣
      originalScheduledChartBlockDifferenceNumerator c bound k i g (-originalScheduledPrefixChartNumerator c bound k T hT) := by
  let h := originalScheduledNonidentityPrimeTorus bound j.val
  exact originalPositiveInvariantFraction_dvd_numerator (originalScheduledPrimeCharacter bound j.val h) _ _ _
    (originalScheduledChartBlockDifferenceDenominator_ne_zero c bound k i g)
    (originalScheduledChartOtherBlock_dvd_difference_denominator c bound k i j hij g)
    (originalScheduledChartOtherBlock_isRelPrime_twisted_difference_denominator c bound k i j hij g h
      (originalScheduledNonidentityPrimeTorus_ne_identity bound j.val))
    (originalScheduledPrefixNegativeChartBlockDifferenceFraction_other_invariant c bound k T hT i j hij g h)

/-- Pairwise actual whole-block relative primality cancels the ENTIRE complementary product,
for EVERY complete original positive cut and ANY selected actual character. -/
theorem originalScheduledPrefixChartComplement_dvd_difference_numerator (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledChartOtherBlocksPolynomial c bound k i ∣
      originalScheduledChartBlockDifferenceNumerator c bound k i g (originalScheduledPrefixChartNumerator c bound k T hT) := by
  classical
  unfold originalScheduledChartOtherBlocksPolynomial
  apply Finset.prod_dvd_of_isRelPrime
  · intro a _ b _ hab
    exact originalScheduledChartBlockPolynomial_other_isRelPrime c bound k a b hab
  · intro j hj
    exact originalScheduledPrefixChartOtherBlock_dvd_difference_numerator c bound k T hT i j
      (Finset.mem_erase.mp hj).1.symm g

/-- The ENTIRE original strict-negative complement cancels with the same genuine pair inputs. -/
theorem originalScheduledPrefixNegativeChartComplement_dvd_difference_numerator (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledChartOtherBlocksPolynomial c bound k i ∣
      originalScheduledChartBlockDifferenceNumerator c bound k i g (-originalScheduledPrefixChartNumerator c bound k T hT) := by
  classical
  unfold originalScheduledChartOtherBlocksPolynomial
  apply Finset.prod_dvd_of_isRelPrime
  · intro a _ b _ hab
    exact originalScheduledChartBlockPolynomial_other_isRelPrime c bound k a b hab
  · intro j hj
    exact originalScheduledPrefixNegativeChartOtherBlock_dvd_difference_numerator c bound k T hT i j
      (Finset.mem_erase.mp hj).1.symm g

/-- A proved complementary divisibility yields the genuine reduced polynomial fraction. -/
theorem originalScheduledChartBlockDifferenceFraction_reduce_of_dvd (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) (R : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hd : originalScheduledChartOtherBlocksPolynomial c bound k i ∣ originalScheduledChartBlockDifferenceNumerator c bound k i g R) :
    ∃ B : AddMonoidAlgebra ℂ (ℕ × ℕ),
      originalScheduledChartBlockDifferenceNumerator c bound k i g R = originalScheduledChartOtherBlocksPolynomial c bound k i * B ∧
      let χ := originalScheduledPrimeCharacter bound i.val g
      let P := originalScheduledPrefixChartPolynomial c bound k
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ P) - f R / f P =
        f B / f (originalScheduledChartBlockPolynomial c bound k i * originalScheduledChartCharacterBlockPolynomial c bound k i g) := by
  obtain ⟨B, hB⟩ := hd
  refine ⟨B, hB, ?_⟩
  dsimp only
  rw [← originalScheduledChartBlockDifferenceFraction_normalize c, hB]
  let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  have hE0 := (map_ne_zero_iff f hinj).mpr (originalScheduledChartOtherBlocksPolynomial_ne_zero c bound k i)
  have hQi0 : f (originalScheduledChartBlockPolynomial c bound k i) ≠ 0 := by
    apply (map_ne_zero_iff f hinj).mpr
    rw [← originalScheduledChartCharacterBlockPolynomial_one c]
    exact originalScheduledChartCharacterBlockPolynomial_ne_zero c bound k i _
  have hQg0 := (map_ne_zero_iff f hinj).mpr (originalScheduledChartCharacterBlockPolynomial_ne_zero c bound k i g)
  simp only [originalScheduledChartBlockDifferenceDenominator, map_mul]
  change f (originalScheduledChartOtherBlocksPolynomial c bound k i) * f B /
    (f (originalScheduledChartBlockPolynomial c bound k i) *
      f (originalScheduledChartCharacterBlockPolynomial c bound k i g) *
      f (originalScheduledChartOtherBlocksPolynomial c bound k i)) =
    f B / (f (originalScheduledChartBlockPolynomial c bound k i) *
      f (originalScheduledChartCharacterBlockPolynomial c bound k i g))
  field_simp [hE0, hQi0, hQg0]

/-- EVERY actual complete original strong pair has its positive character difference represented
using ONLY the selected original block and its translate in the denominator. All inputs are internal. -/
theorem originalScheduledPrefixChartBlockDifferenceFraction_reduced (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    ∃ B : AddMonoidAlgebra ℂ (ℕ × ℕ),
      originalScheduledChartBlockDifferenceNumerator c bound k i g (originalScheduledPrefixChartNumerator c bound k T hT) =
        originalScheduledChartOtherBlocksPolynomial c bound k i * B ∧
      let χ := originalScheduledPrimeCharacter bound i.val g
      let P := originalScheduledPrefixChartPolynomial c bound k
      let R := originalScheduledPrefixChartNumerator c bound k T hT
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ P) - f R / f P =
        f B / f (originalScheduledChartBlockPolynomial c bound k i * originalScheduledChartCharacterBlockPolynomial c bound k i g) :=
  originalScheduledChartBlockDifferenceFraction_reduce_of_dvd c bound k i g _
    (originalScheduledPrefixChartComplement_dvd_difference_numerator c bound k T hT i g)

/-- EVERY actual strict negative cut has the same reduced denominator and exact original sign. -/
theorem originalScheduledPrefixNegativeChartBlockDifferenceFraction_reduced (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    ∃ B : AddMonoidAlgebra ℂ (ℕ × ℕ),
      originalScheduledChartBlockDifferenceNumerator c bound k i g (-originalScheduledPrefixChartNumerator c bound k T hT) =
        originalScheduledChartOtherBlocksPolynomial c bound k i * B ∧
      let χ := originalScheduledPrimeCharacter bound i.val g
      let P := originalScheduledPrefixChartPolynomial c bound k
      let R := -originalScheduledPrefixChartNumerator c bound k T hT
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ P) - f R / f P =
        f B / f (originalScheduledChartBlockPolynomial c bound k i * originalScheduledChartCharacterBlockPolynomial c bound k i g) :=
  originalScheduledChartBlockDifferenceFraction_reduce_of_dvd c bound k i g _
    (originalScheduledPrefixNegativeChartComplement_dvd_difference_numerator c bound k T hT i g)

end
end MeyerGeneralProblem.StrongParity
