module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalBoundedDivisibility

@[expose] public section

/-! Private invariance of EVERY actual globally bounded separate-pole lift.
Original whole-block cancellation supplies divisibility; exact full-square
bounds and the origin coefficient kill the constant quotient internally. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Every genuine integer unit character fixes the literal origin coefficient. -/
theorem originalPositiveCharacterTwist_origin
    (χ : Multiplicative (ℤ × ℤ) →* ℂˣ) (u : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    (originalPositiveCharacterTwist χ u).coeff (0, 0) = u.coeff (0, 0) := by
  rw [originalPositiveCharacterTwist_coefficient]
  change (χ 1 : ℂ) * u.coeff (0, 0) = u.coeff (0, 0)
  rw [map_one, Units.val_one, one_mul]

/-- Exact algebraic divisibility of the selected-lift difference. The actual
prefix application below derives all complementary identities and prime facts. -/
theorem originalPositiveSplit_character_difference_divisible
    (χ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (q e a b r u v : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hr : r = e * u + q * v)
    (hq : originalPositiveCharacterTwist χ q = q)
    (he : originalPositiveCharacterTwist χ e * a = e * b)
    (hrel : IsRelPrime q (e * b))
    (hdiv : q ∣ originalPositiveCharacterTwist χ r * a - r * b) :
    q ∣ originalPositiveCharacterTwist χ u - u := by
  have hn : originalPositiveCharacterTwist χ r * a - r * b =
      e * b * (originalPositiveCharacterTwist χ u - u) +
        q * (a * originalPositiveCharacterTwist χ v - b * v) := by
    rw [hr, map_add, map_mul, map_mul, hq]
    calc
      (originalPositiveCharacterTwist χ e * originalPositiveCharacterTwist χ u +
        q * originalPositiveCharacterTwist χ v) * a - (e * u + q * v) * b =
          (originalPositiveCharacterTwist χ e * a) * originalPositiveCharacterTwist χ u -
            (e * b) * u + q * (a * originalPositiveCharacterTwist χ v - b * v) := by ring
      _ = _ := by rw [he]; ring
  have hd := hdiv.sub (dvd_mul_right q (a * originalPositiveCharacterTwist χ v - b * v))
  have hs : (originalPositiveCharacterTwist χ r * a - r * b) -
      q * (a * originalPositiveCharacterTwist χ v - b * v) =
        e * b * (originalPositiveCharacterTwist χ u - u) := by rw [hn]; ring
  rw [hs] at hd
  exact hrel.dvd_of_dvd_mul_left hd

/-- The actual complementary character identity follows by canceling the
nonzero selected block from TWO exact complete-prefix factorizations. -/
theorem originalScheduledComplement_cross_character (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound j.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g)
        (originalScheduledOtherBlocksPolynomial bound k i) * originalScheduledBlockPositivePolynomial bound k j =
      originalScheduledOtherBlocksPolynomial bound k i * originalScheduledCharacterBlockPolynomial bound k j g := by
  let χ := originalScheduledPrimeCharacter bound j.val g
  have hq := originalScheduledPositiveBlock_other_character_invariant bound k j i hij.symm g
  have hq0 : originalScheduledBlockPositivePolynomial bound k i ≠ 0 := by
    rw [← originalScheduledCharacterBlockPolynomial_one]
    exact originalScheduledCharacterBlockPolynomial_ne_zero bound k i _
  have ht : originalScheduledBlockPositivePolynomial bound k i *
      originalPositiveCharacterTwist χ (originalScheduledOtherBlocksPolynomial bound k i) =
      originalPositiveCharacterTwist χ (originalScheduledPrefixPolynomial bound k) := by
    rw [originalScheduledPrefixPolynomial_block_complement bound k i, map_mul, hq]
  apply mul_left_cancel₀ hq0
  calc
    originalScheduledBlockPositivePolynomial bound k i *
        (originalPositiveCharacterTwist χ (originalScheduledOtherBlocksPolynomial bound k i) *
          originalScheduledBlockPositivePolynomial bound k j) =
      originalPositiveCharacterTwist χ (originalScheduledPrefixPolynomial bound k) *
        originalScheduledBlockPositivePolynomial bound k j := by rw [← ht]; ring
    _ = originalScheduledPrefixPolynomial bound k * originalScheduledCharacterBlockPolynomial bound k j g := by
      rw [originalScheduledPrefixPolynomial_character_factorization bound k j g,
        originalScheduledPrefixPolynomial_block_complement bound k j]
      ring
    _ = _ := by rw [originalScheduledPrefixPolynomial_block_complement bound k i]; ring

/-- EVERY globally bounded selected numerator of the ACTUAL original root
component is fixed by ANY other private group. No invariance certificate input. -/
theorem originalScheduledPrefixGlobalLift_other_invariant (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound j.val)
    (u v : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hu : OriginalPositiveInSquare u (originalScheduledChartBlockDegree bound k i))
    (hr : originalScheduledPrefixPositiveNumerator bound k T hT =
      originalScheduledOtherBlocksPolynomial bound k i * u + originalScheduledBlockPositivePolynomial bound k i * v) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g) u = u := by
  let χ := originalScheduledPrimeCharacter bound j.val g
  have hrelE : IsRelPrime (originalScheduledBlockPositivePolynomial bound k i)
      (originalScheduledOtherBlocksPolynomial bound k i) := by
    rw [← originalScheduledCharacterBlockPolynomial_one]
    exact originalScheduledCharacterBlock_complement_isRelPrime bound k i _
  have hrelJ : IsRelPrime (originalScheduledBlockPositivePolynomial bound k i)
      (originalScheduledCharacterBlockPolynomial bound k j g) := by
    rw [← originalScheduledCharacterBlockPolynomial_one]
    exact originalScheduledCharacterBlocks_other_block_isRelPrime bound k i j hij _ g
  have hdiv : originalScheduledBlockPositivePolynomial bound k i ∣
      originalPositiveCharacterTwist χ u - u :=
    originalPositiveSplit_character_difference_divisible χ _ _ _ _ _ u v hr
      (originalScheduledPositiveBlock_other_character_invariant bound k j i hij.symm g)
      (originalScheduledComplement_cross_character bound k i j hij g)
      (hrelE.mul_right hrelJ)
      (originalScheduledPrefixOtherBlock_dvd_difference_numerator bound k T hT j i hij.symm g)
  have h0 : (originalScheduledBlockPositivePolynomial bound k i).coeff (0, 0) ≠ 0 := by
    simpa only [originalScheduledChartBlockPolynomial, originalPositiveChartReflection_affine] using
      originalScheduledChartBlockPolynomial_origin_ne_zero (false, false) bound k i
  apply sub_eq_zero.mp
  apply originalPositive_bounded_divisor_zero_origin _ _ _
    (originalScheduledBlockPositivePolynomial_inSquare bound k i)
    (originalPositiveInSquare_sub _ _ _ (originalPositiveInSquare_twist χ u _ hu) hu)
    h0 (originalScheduledBlockPositivePolynomial_top_ne_zero bound k i) hdiv
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, originalPositiveCharacterTwist_origin, sub_self]

/-- EVERY actual complete pair has a global selected/complement split whose
selected numerator is invariant under ALL other private groups, internally. -/
theorem originalScheduledPrefixNumerator_invariant_split (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (i : Fin k) :
    ∃ u v : AddMonoidAlgebra ℂ (ℕ × ℕ),
      OriginalPositiveInSquare u (originalScheduledChartBlockDegree bound k i) ∧
      OriginalPositiveInSquare v (originalScheduledChartOtherDegree bound k i) ∧
      originalScheduledPrefixPositiveNumerator bound k T hT =
        originalScheduledOtherBlocksPolynomial bound k i * u + originalScheduledBlockPositivePolynomial bound k i * v ∧
      ∀ (j : Fin k), i ≠ j → ∀ g : OriginalScheduledPrimeTorus bound j.val,
        originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g) u = u := by
  obtain ⟨u, v, hu, hv, hr⟩ := originalScheduledPrefixNumerator_global_split bound k T hT i
  exact ⟨u, v, hu, hv, hr, fun j hij g =>
    originalScheduledPrefixGlobalLift_other_invariant bound k T hT i j hij g u v hu hr⟩

/-- The strict-negative original cut has the same genuine internally invariant
split, with its exact sign and both original global square bounds retained. -/
theorem originalScheduledPrefixNegativeNumerator_invariant_split (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (i : Fin k) :
    ∃ u v : AddMonoidAlgebra ℂ (ℕ × ℕ),
      OriginalPositiveInSquare u (originalScheduledChartBlockDegree bound k i) ∧
      OriginalPositiveInSquare v (originalScheduledChartOtherDegree bound k i) ∧
      -originalScheduledPrefixPositiveNumerator bound k T hT =
        originalScheduledOtherBlocksPolynomial bound k i * u + originalScheduledBlockPositivePolynomial bound k i * v ∧
      ∀ (j : Fin k), i ≠ j → ∀ g : OriginalScheduledPrimeTorus bound j.val,
        originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g) u = u := by
  obtain ⟨u, v, hu, hv, hr, hinv⟩ := originalScheduledPrefixNumerator_invariant_split bound k T hT i
  refine ⟨-u, -v, originalPositiveInSquare_neg _ _ hu, originalPositiveInSquare_neg _ _ hv, ?_, ?_⟩
  · rw [hr]; ring
  · intro j hij g
    rw [map_neg, hinv j hij g]

end
end MeyerGeneralProblem.StrongParity
