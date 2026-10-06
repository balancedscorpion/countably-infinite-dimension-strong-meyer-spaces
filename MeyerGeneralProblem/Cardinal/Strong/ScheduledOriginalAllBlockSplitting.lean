module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalTopCornerNormalization

@[expose] public section

/-! Exact ALL-block normalized decomposition of EVERY complete original finite
prefix root component, for BOTH cuts. Private invariance and compatibility are
derived internally. Native exponent descent and complete source reconstruction
remain separate obligations; the original cone/root companion is retained. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- All coefficient collisions in a finite sum retain the common original box. -/
theorem originalPositiveInSquare_sum {ι : Type*} (s : Finset ι)
    (p : ι → AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ℕ)
    (hp : ∀ i ∈ s, OriginalPositiveInSquare (p i) d) :
    OriginalPositiveInSquare (∑ i ∈ s, p i) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using originalPositiveInSquare_zero d
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact originalPositiveInSquare_add _ _ d (hp a (Finset.mem_insert_self a s))
      (ih (fun i hi => hp i (Finset.mem_insert_of_mem hi)))

/-- The complete actual prefix has a nonzero origin coefficient, including
the empty prefix. No nonzero-corner certificate is supplied. -/
theorem originalScheduledPrefixPolynomial_origin_ne_zero (bound : ℕ → ℕ) (k : ℕ) :
    (originalScheduledPrefixPolynomial bound k).coeff (0, 0) ≠ 0 := by
  rw [← originalPositiveTorusEvaluation_origin, originalScheduledPrefixPolynomial_eq_block_product, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [originalPositiveTorusEvaluation_origin]
  simpa only [originalScheduledChartBlockPolynomial, originalPositiveChartReflection_affine] using
    originalScheduledChartBlockPolynomial_origin_ne_zero (false, false) bound k i

/-- The complete actual prefix has a nonzero FULL top coefficient, derived
from all actual block corners and their literal sum of degrees. -/
theorem originalScheduledPrefixPolynomial_top_ne_zero (bound : ℕ → ℕ) (k : ℕ) :
    (originalScheduledPrefixPolynomial bound k).coeff
      (originalScheduledPrefixPolynomialDegree bound k, originalScheduledPrefixPolynomialDegree bound k) ≠ 0 := by
  rw [originalScheduledPrefixPolynomial_eq_block_product]
  change (∏ i : Fin k, originalScheduledBlockPositivePolynomial bound k i).coeff
    (∑ i : Fin k, originalScheduledChartBlockDegree bound k i,
      ∑ i : Fin k, originalScheduledChartBlockDegree bound k i) ≠ 0
  rw [originalPositive_prod_top_coeff Finset.univ _ _
    (fun i _ => originalScheduledBlockPositivePolynomial_inSquare bound k i)]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => originalScheduledBlockPositivePolynomial_top_ne_zero bound k i)

/-- The original complete root-component numerator has the literal missing
top coefficient, before ANY raw physical or spectral restriction. -/
theorem originalScheduledPrefixPositiveNumerator_top_zero (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    (originalScheduledPrefixPositiveNumerator bound k T hT).coeff
      (originalScheduledPrefixPolynomialDegree bound k, originalScheduledPrefixPolynomialDegree bound k) = 0 := by
  by_contra hc
  exact (originalScheduledPrefixPositiveNumerator_support_box bound k T hT
    (Finsupp.mem_support_iff.mpr hc)).2.2 rfl

/-- ALL exact selected/complement splits imply divisibility of their common
residual by the complete actual prefix. Compatibility is algebraically derived. -/
theorem originalScheduledAllBlock_residual_dvd (bound : ℕ → ℕ) (k : ℕ)
    (r : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (u v : Fin k → AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hr : ∀ i, r = originalScheduledOtherBlocksPolynomial bound k i * u i +
      originalScheduledBlockPositivePolynomial bound k i * v i) :
    originalScheduledPrefixPolynomial bound k ∣
      r - ∑ i : Fin k, originalScheduledOtherBlocksPolynomial bound k i * u i := by
  classical
  rw [originalScheduledPrefixPolynomial_eq_block_product]
  apply Finset.prod_dvd_of_isRelPrime
  · intro i _ j _ hij
    exact originalScheduledBlockPositivePolynomial_other_isRelPrime bound k i j hij
  · intro i _
    have hrest : originalScheduledBlockPositivePolynomial bound k i ∣
        ∑ j ∈ Finset.univ.erase i, originalScheduledOtherBlocksPolynomial bound k j * u j := by
      apply Finset.dvd_sum
      intro j hj
      exact (originalScheduledOtherBlock_dvd_complement bound k j i (Finset.mem_erase.mp hj).1).mul_right _
    have hi : originalScheduledBlockPositivePolynomial bound k i ∣
        r - originalScheduledOtherBlocksPolynomial bound k i * u i := by
      rw [hr i]
      convert dvd_mul_right (originalScheduledBlockPositivePolynomial bound k i) (v i) using 1
      ring
    have hs : r - ∑ j : Fin k, originalScheduledOtherBlocksPolynomial bound k j * u j =
        (r - originalScheduledOtherBlocksPolynomial bound k i * u i) -
          ∑ j ∈ Finset.univ.erase i, originalScheduledOtherBlocksPolynomial bound k j * u j := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun j : Fin k => originalScheduledOtherBlocksPolynomial bound k j * u j) (Finset.mem_univ i)]
      ring
    rw [hs]
    exact hi.sub hrest

/-- EVERY complete actual original pair has an exact ALL-block decomposition
with actual individual boxes, zero top corners and ALL other-group invariances.
No invariance, normalization, residual or ALL-block compatibility input survives. -/
theorem originalScheduledPrefixNumerator_all_block_split (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ u : Fin k → AddMonoidAlgebra ℂ (ℕ × ℕ),
      (∀ i, OriginalPositiveInSquare (u i) (originalScheduledChartBlockDegree bound k i) ∧
        (u i).coeff (originalScheduledChartBlockDegree bound k i, originalScheduledChartBlockDegree bound k i) = 0 ∧
        ∀ (j : Fin k), i ≠ j → ∀ g : OriginalScheduledPrimeTorus bound j.val,
          originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g) (u i) = u i) ∧
      originalScheduledPrefixPositiveNumerator bound k T hT =
        ∑ i : Fin k, originalScheduledOtherBlocksPolynomial bound k i * u i := by
  classical
  choose u v hu hv hr hinv using (fun i : Fin k => originalScheduledPrefixNumerator_invariant_split bound k T hT i)
  let n (i : Fin k) := originalPositiveRemoveTop (originalScheduledChartBlockDegree bound k i)
    (originalScheduledBlockPositivePolynomial bound k i) (u i)
  have hn (i : Fin k) : OriginalPositiveInSquare (n i) (originalScheduledChartBlockDegree bound k i) :=
    originalPositiveRemoveTop_inSquare _ _ _ (originalScheduledBlockPositivePolynomial_inSquare bound k i) (hu i)
  have ht (i : Fin k) : (n i).coeff
      (originalScheduledChartBlockDegree bound k i, originalScheduledChartBlockDegree bound k i) = 0 :=
    originalPositiveRemoveTop_top_zero _ _ _ (originalScheduledBlockPositivePolynomial_top_ne_zero bound k i)
  have hi (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound j.val) :
      originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g) (n i) = n i :=
    originalPositiveRemoveTop_character_invariant _ _ _ _
      (originalScheduledPositiveBlock_other_character_invariant bound k j i hij.symm g) (hinv i j hij g)
  let w (i : Fin k) := v i + originalScheduledOtherBlocksPolynomial bound k i *
    AddMonoidAlgebra.single (0, 0) ((u i).coeff
      (originalScheduledChartBlockDegree bound k i, originalScheduledChartBlockDegree bound k i) /
        (originalScheduledBlockPositivePolynomial bound k i).coeff
          (originalScheduledChartBlockDegree bound k i, originalScheduledChartBlockDegree bound k i))
  have hs (i : Fin k) : originalScheduledPrefixPositiveNumerator bound k T hT =
      originalScheduledOtherBlocksPolynomial bound k i * n i + originalScheduledBlockPositivePolynomial bound k i * w i :=
    originalPositiveRemoveTop_split _ _ _ _ _ _ (hr i)
  let sumN := ∑ i : Fin k, originalScheduledOtherBlocksPolynomial bound k i * n i
  have hsum : OriginalPositiveInSquare sumN (originalScheduledPrefixPolynomialDegree bound k) := by
    apply originalPositiveInSquare_sum
    intro i _
    rw [← originalScheduledChartDegrees_sum bound k i, Nat.add_comm]
    exact originalPositiveInSquare_mul _ _ _ _ (originalScheduledOtherBlocksPolynomial_inSquare bound k i) (hn i)
  have hsumTop : sumN.coeff
      (originalScheduledPrefixPolynomialDegree bound k, originalScheduledPrefixPolynomialDegree bound k) = 0 := by
    simp only [sumN, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [← originalScheduledChartDegrees_sum bound k i, Nat.add_comm,
      originalPositive_product_top_coeff _ _ _ _ (originalScheduledOtherBlocksPolynomial_inSquare bound k i) (hn i),
      ht i, mul_zero]
  have hz : originalScheduledPrefixPositiveNumerator bound k T hT - sumN = 0 :=
    originalPositive_bounded_divisor_zero_top _ _ _
      (originalScheduledPrefixPolynomial_inSquare bound k)
      (originalPositiveInSquare_sub _ _ _ (originalScheduledPrefixPositiveNumerator_inSquare bound k T hT) hsum)
      (originalScheduledPrefixPolynomial_origin_ne_zero bound k) (originalScheduledPrefixPolynomial_top_ne_zero bound k)
      (originalScheduledAllBlock_residual_dvd bound k _ n w hs)
      (by rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
        originalScheduledPrefixPositiveNumerator_top_zero bound k T hT, hsumTop, sub_self])
  exact ⟨n, fun i => ⟨hn i, ht i, hi i⟩, sub_eq_zero.mp hz⟩

/-- The strict-negative actual root component has the exact same ALL-block
normal form, with the original sign and EVERY coefficient box retained. -/
theorem originalScheduledPrefixNegativeNumerator_all_block_split (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ u : Fin k → AddMonoidAlgebra ℂ (ℕ × ℕ),
      (∀ i, OriginalPositiveInSquare (u i) (originalScheduledChartBlockDegree bound k i) ∧
        (u i).coeff (originalScheduledChartBlockDegree bound k i, originalScheduledChartBlockDegree bound k i) = 0 ∧
        ∀ (j : Fin k), i ≠ j → ∀ g : OriginalScheduledPrimeTorus bound j.val,
          originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g) (u i) = u i) ∧
      -originalScheduledPrefixPositiveNumerator bound k T hT =
        ∑ i : Fin k, originalScheduledOtherBlocksPolynomial bound k i * u i := by
  obtain ⟨u, hu, hr⟩ := originalScheduledPrefixNumerator_all_block_split bound k T hT
  refine ⟨fun i => -u i, ?_, ?_⟩
  · intro i
    refine ⟨originalPositiveInSquare_neg _ _ (hu i).1, ?_, ?_⟩
    · simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, (hu i).2.1, neg_zero]
    · intro j hij g
      rw [map_neg, (hu i).2.2 j hij g]
  · rw [hr]
    simp only [mul_neg, Finset.sum_neg_distrib]

/-- A genuine ALL-block original numerator identity gives its exact fraction
sum, with every nonzero actual divisor derived internally. -/
theorem originalScheduledAllBlock_fraction_sum (bound : ℕ → ℕ) (k : ℕ)
    (r : AddMonoidAlgebra ℂ (ℕ × ℕ)) (u : Fin k → AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hr : r = ∑ i : Fin k, originalScheduledOtherBlocksPolynomial bound k i * u i) :
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f r / f (originalScheduledPrefixPolynomial bound k) =
      ∑ i : Fin k, f (u i) / f (originalScheduledBlockPositivePolynomial bound k i) := by
  let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
  have hf : Function.Injective f := IsFractionRing.injective _ _
  dsimp only
  rw [hr, map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hq : f (originalScheduledBlockPositivePolynomial bound k i) ≠ 0 := by
    apply (map_ne_zero_iff f hf).mpr
    rw [← originalScheduledCharacterBlockPolynomial_one]
    exact originalScheduledCharacterBlockPolynomial_ne_zero bound k i _
  have he := (map_ne_zero_iff f hf).mpr (originalScheduledOtherBlocksPolynomial_ne_zero bound k i)
  rw [originalScheduledPrefixPolynomial_block_complement bound k i, map_mul, map_mul]
  change f (originalScheduledOtherBlocksPolynomial bound k i) * f (u i) /
    (f (originalScheduledBlockPositivePolynomial bound k i) * f (originalScheduledOtherBlocksPolynomial bound k i)) =
      f (u i) / f (originalScheduledBlockPositivePolynomial bound k i)
  field_simp [hq, he]

/-- EVERY complete actual original positive cut has an exact ALL-block fraction
sum, with full block boxes, missing individual top corners and private invariance. -/
theorem originalScheduledPrefixFraction_all_block_split (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ u : Fin k → AddMonoidAlgebra ℂ (ℕ × ℕ),
      (∀ i, OriginalPositiveInSquare (u i) (originalScheduledChartBlockDegree bound k i) ∧
        (u i).coeff (originalScheduledChartBlockDegree bound k i, originalScheduledChartBlockDegree bound k i) = 0 ∧
        ∀ (j : Fin k), i ≠ j → ∀ g : OriginalScheduledPrimeTorus bound j.val,
          originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g) (u i) = u i) ∧
      originalScheduledPrefixPositiveNumerator bound k T hT =
        ∑ i : Fin k, originalScheduledOtherBlocksPolynomial bound k i * u i ∧
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (originalScheduledPrefixPositiveNumerator bound k T hT) / f (originalScheduledPrefixPolynomial bound k) =
        ∑ i : Fin k, f (u i) / f (originalScheduledBlockPositivePolynomial bound k i) := by
  obtain ⟨u, hu, hr⟩ := originalScheduledPrefixNumerator_all_block_split bound k T hT
  exact ⟨u, hu, hr, originalScheduledAllBlock_fraction_sum bound k _ u hr⟩

/-- EVERY actual strict-negative cut has the same internally derived ALL-block
fraction sum, with the exact original sign and full coefficient scope retained. -/
theorem originalScheduledPrefixNegativeFraction_all_block_split (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ u : Fin k → AddMonoidAlgebra ℂ (ℕ × ℕ),
      (∀ i, OriginalPositiveInSquare (u i) (originalScheduledChartBlockDegree bound k i) ∧
        (u i).coeff (originalScheduledChartBlockDegree bound k i, originalScheduledChartBlockDegree bound k i) = 0 ∧
        ∀ (j : Fin k), i ≠ j → ∀ g : OriginalScheduledPrimeTorus bound j.val,
          originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g) (u i) = u i) ∧
      -originalScheduledPrefixPositiveNumerator bound k T hT =
        ∑ i : Fin k, originalScheduledOtherBlocksPolynomial bound k i * u i ∧
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (-originalScheduledPrefixPositiveNumerator bound k T hT) / f (originalScheduledPrefixPolynomial bound k) =
        ∑ i : Fin k, f (u i) / f (originalScheduledBlockPositivePolynomial bound k i) := by
  obtain ⟨u, hu, hr⟩ := originalScheduledPrefixNegativeNumerator_all_block_split bound k T hT
  exact ⟨u, hu, hr, originalScheduledAllBlock_fraction_sum bound k _ u hr⟩

end
end MeyerGeneralProblem.StrongParity
