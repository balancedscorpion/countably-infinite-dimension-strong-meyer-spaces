module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalDifferencePolynomials

@[expose] public section

/-! EVERY complete actual original finite-prefix strong pair has all other-block
factors canceled from each genuine character difference. The nonidentity other
character, mixed invariance, relative primality and quotient are internal. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- An actual nonidentity two-coordinate character, constructed from the stored primitive root. -/
def originalScheduledNonidentityPrimeTorus (bound : ℕ → ℕ) (i : ℕ) :
    OriginalScheduledPrimeTorus bound i := (originalScheduledPrimitiveRoot bound i, 1)

/-- The actual prime bound and primitive order prove that the constructed character is nonidentity. -/
theorem originalScheduledNonidentityPrimeTorus_ne_identity (bound : ℕ → ℕ) (i : ℕ) :
    originalScheduledNonidentityPrimeTorus bound i ≠ originalScheduledPrimeTorusIdentity bound i := by
  intro he
  have hc := congrArg (fun g : OriginalScheduledPrimeTorus bound i => (g.1.val : ℂ)) he
  change ((originalScheduledPrimitiveRoot bound i).val : ℂ) = 1 at hc
  exact (originalScheduledPrimitiveRoot_isPrimitive bound i).ne_one
    (lt_of_lt_of_le (by decide : 1 < 3) (originalScheduledBlockPrime_three_le bound i)) hc

/-- Every other actual whole block divides the literal complementary product. -/
theorem originalScheduledOtherBlock_dvd_complement (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) :
    originalScheduledBlockPositivePolynomial bound k j ∣ originalScheduledOtherBlocksPolynomial bound k i := by
  classical
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)

/-- Every other actual whole block divides the genuine uncanceled difference denominator. -/
theorem originalScheduledOtherBlock_dvd_difference_denominator (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledBlockPositivePolynomial bound k j ∣ originalScheduledBlockDifferenceDenominator bound k i g :=
  (originalScheduledOtherBlock_dvd_complement bound k i j hij).mul_left _

/-- A nonidentity actual other character makes its whole block relatively prime to
the twisted complete difference denominator, with all original factors retained. -/
theorem originalScheduledOtherBlock_isRelPrime_twisted_difference_denominator
    (bound : ℕ → ℕ) (k : ℕ) (i j : Fin k) (hij : i ≠ j)
    (g : OriginalScheduledPrimeTorus bound i.val) (h : OriginalScheduledPrimeTorus bound j.val)
    (hh : h ≠ originalScheduledPrimeTorusIdentity bound j.val) :
    IsRelPrime (originalScheduledBlockPositivePolynomial bound k j)
      (originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val h)
        (originalScheduledBlockDifferenceDenominator bound k i g)) := by
  classical
  have hQi := originalScheduledBlockPositivePolynomial_other_isRelPrime bound k j i hij.symm
  have hQg : IsRelPrime (originalScheduledBlockPositivePolynomial bound k j)
      (originalScheduledCharacterBlockPolynomial bound k i g) := by
    rw [← originalScheduledCharacterBlockPolynomial_one]
    exact originalScheduledCharacterBlocks_other_block_isRelPrime bound k j i hij.symm _ g
  have hE : IsRelPrime (originalScheduledBlockPositivePolynomial bound k j)
      (originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val h)
        (originalScheduledOtherBlocksPolynomial bound k i)) := by
    unfold originalScheduledOtherBlocksPolynomial
    rw [map_prod]
    apply IsRelPrime.prod_right
    intro t _
    by_cases htj : t = j
    · subst t
      rw [originalScheduledPositiveBlock_character_twist, ← originalScheduledCharacterBlockPolynomial_one]
      exact originalScheduledCharacterBlocks_same_block_isRelPrime bound k j _ h hh.symm
    · rw [originalScheduledPositiveBlock_other_character_invariant bound k j t (Ne.symm htj) h]
      exact originalScheduledBlockPositivePolynomial_other_isRelPrime bound k j t (Ne.symm htj)
  simp only [originalScheduledBlockDifferenceDenominator, map_mul,
    originalScheduledPositiveBlock_other_character_invariant bound k j i hij.symm h,
    originalScheduledPositiveCharacterBlock_other_invariant bound k j i hij.symm h g]
  exact (hQi.mul_right hQg).mul_right hE

/-- EVERY actual complete original positive-cut difference numerator is divisible by each other whole block. -/
theorem originalScheduledPrefixOtherBlock_dvd_difference_numerator (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledBlockPositivePolynomial bound k j ∣
      originalScheduledBlockDifferenceNumerator bound k i g (originalScheduledPrefixPositiveNumerator bound k T hT) := by
  let h := originalScheduledNonidentityPrimeTorus bound j.val
  exact originalPositiveInvariantFraction_dvd_numerator (originalScheduledPrimeCharacter bound j.val h) _ _ _
    (originalScheduledBlockDifferenceDenominator_ne_zero bound k i g)
    (originalScheduledOtherBlock_dvd_difference_denominator bound k i j hij g)
    (originalScheduledOtherBlock_isRelPrime_twisted_difference_denominator bound k i j hij g h
      (originalScheduledNonidentityPrimeTorus_ne_identity bound j.val))
    (originalScheduledPrefixBlockDifferenceFraction_other_invariant bound k T hT i j hij g h)

/-- The strict original negative-cut difference has the same internally derived whole-block divisibility. -/
theorem originalScheduledPrefixNegativeOtherBlock_dvd_difference_numerator (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledBlockPositivePolynomial bound k j ∣
      originalScheduledBlockDifferenceNumerator bound k i g (-originalScheduledPrefixPositiveNumerator bound k T hT) := by
  let h := originalScheduledNonidentityPrimeTorus bound j.val
  exact originalPositiveInvariantFraction_dvd_numerator (originalScheduledPrimeCharacter bound j.val h) _ _ _
    (originalScheduledBlockDifferenceDenominator_ne_zero bound k i g)
    (originalScheduledOtherBlock_dvd_difference_denominator bound k i j hij g)
    (originalScheduledOtherBlock_isRelPrime_twisted_difference_denominator bound k i j hij g h
      (originalScheduledNonidentityPrimeTorus_ne_identity bound j.val))
    (originalScheduledPrefixNegativeBlockDifferenceFraction_other_invariant bound k T hT i j hij g h)

/-- Pairwise actual whole-block relative primality cancels the ENTIRE complementary product,
for EVERY complete original positive cut and ANY selected actual character. -/
theorem originalScheduledPrefixComplement_dvd_difference_numerator (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledOtherBlocksPolynomial bound k i ∣
      originalScheduledBlockDifferenceNumerator bound k i g (originalScheduledPrefixPositiveNumerator bound k T hT) := by
  classical
  unfold originalScheduledOtherBlocksPolynomial
  apply Finset.prod_dvd_of_isRelPrime
  · intro a _ b _ hab
    exact originalScheduledBlockPositivePolynomial_other_isRelPrime bound k a b hab
  · intro j hj
    exact originalScheduledPrefixOtherBlock_dvd_difference_numerator bound k T hT i j
      (Finset.mem_erase.mp hj).1.symm g

/-- The ENTIRE original strict-negative complement cancels with the same genuine pair inputs. -/
theorem originalScheduledPrefixNegativeComplement_dvd_difference_numerator (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledOtherBlocksPolynomial bound k i ∣
      originalScheduledBlockDifferenceNumerator bound k i g (-originalScheduledPrefixPositiveNumerator bound k T hT) := by
  classical
  unfold originalScheduledOtherBlocksPolynomial
  apply Finset.prod_dvd_of_isRelPrime
  · intro a _ b _ hab
    exact originalScheduledBlockPositivePolynomial_other_isRelPrime bound k a b hab
  · intro j hj
    exact originalScheduledPrefixNegativeOtherBlock_dvd_difference_numerator bound k T hT i j
      (Finset.mem_erase.mp hj).1.symm g

/-- A proved complementary divisibility yields the genuine reduced polynomial fraction. -/
theorem originalScheduledBlockDifferenceFraction_reduce_of_dvd (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) (R : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hd : originalScheduledOtherBlocksPolynomial bound k i ∣ originalScheduledBlockDifferenceNumerator bound k i g R) :
    ∃ B : AddMonoidAlgebra ℂ (ℕ × ℕ),
      originalScheduledBlockDifferenceNumerator bound k i g R = originalScheduledOtherBlocksPolynomial bound k i * B ∧
      let χ := originalScheduledPrimeCharacter bound i.val g
      let P := originalScheduledPrefixPolynomial bound k
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ P) - f R / f P =
        f B / f (originalScheduledBlockPositivePolynomial bound k i * originalScheduledCharacterBlockPolynomial bound k i g) := by
  obtain ⟨B, hB⟩ := hd
  refine ⟨B, hB, ?_⟩
  dsimp only
  rw [← originalScheduledBlockDifferenceFraction_normalize, hB]
  let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  have hE0 := (map_ne_zero_iff f hinj).mpr (originalScheduledOtherBlocksPolynomial_ne_zero bound k i)
  have hQi0 : f (originalScheduledBlockPositivePolynomial bound k i) ≠ 0 := by
    apply (map_ne_zero_iff f hinj).mpr
    rw [← originalScheduledCharacterBlockPolynomial_one]
    exact originalScheduledCharacterBlockPolynomial_ne_zero bound k i _
  have hQg0 := (map_ne_zero_iff f hinj).mpr (originalScheduledCharacterBlockPolynomial_ne_zero bound k i g)
  simp only [originalScheduledBlockDifferenceDenominator, map_mul]
  change f (originalScheduledOtherBlocksPolynomial bound k i) * f B /
    (f (originalScheduledBlockPositivePolynomial bound k i) *
      f (originalScheduledCharacterBlockPolynomial bound k i g) *
      f (originalScheduledOtherBlocksPolynomial bound k i)) =
    f B / (f (originalScheduledBlockPositivePolynomial bound k i) *
      f (originalScheduledCharacterBlockPolynomial bound k i g))
  field_simp [hE0, hQi0, hQg0]

/-- EVERY actual complete original strong pair has its positive character difference represented
using ONLY the selected original block and its translate in the denominator. All inputs are internal. -/
theorem originalScheduledPrefixBlockDifferenceFraction_reduced (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    ∃ B : AddMonoidAlgebra ℂ (ℕ × ℕ),
      originalScheduledBlockDifferenceNumerator bound k i g (originalScheduledPrefixPositiveNumerator bound k T hT) =
        originalScheduledOtherBlocksPolynomial bound k i * B ∧
      let χ := originalScheduledPrimeCharacter bound i.val g
      let P := originalScheduledPrefixPolynomial bound k
      let R := originalScheduledPrefixPositiveNumerator bound k T hT
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ P) - f R / f P =
        f B / f (originalScheduledBlockPositivePolynomial bound k i * originalScheduledCharacterBlockPolynomial bound k i g) :=
  originalScheduledBlockDifferenceFraction_reduce_of_dvd bound k i g _
    (originalScheduledPrefixComplement_dvd_difference_numerator bound k T hT i g)

/-- EVERY actual strict negative cut has the same reduced denominator and exact original sign. -/
theorem originalScheduledPrefixNegativeBlockDifferenceFraction_reduced (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    ∃ B : AddMonoidAlgebra ℂ (ℕ × ℕ),
      originalScheduledBlockDifferenceNumerator bound k i g (-originalScheduledPrefixPositiveNumerator bound k T hT) =
        originalScheduledOtherBlocksPolynomial bound k i * B ∧
      let χ := originalScheduledPrimeCharacter bound i.val g
      let P := originalScheduledPrefixPolynomial bound k
      let R := -originalScheduledPrefixPositiveNumerator bound k T hT
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ P) - f R / f P =
        f B / f (originalScheduledBlockPositivePolynomial bound k i * originalScheduledCharacterBlockPolynomial bound k i g) :=
  originalScheduledBlockDifferenceFraction_reduce_of_dvd bound k i g _
    (originalScheduledPrefixNegativeComplement_dvd_difference_numerator bound k T hT i g)

end
end MeyerGeneralProblem.StrongParity
