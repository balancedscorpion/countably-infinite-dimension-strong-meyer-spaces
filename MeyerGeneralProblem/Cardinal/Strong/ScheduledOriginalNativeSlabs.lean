module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalNativeSlabDescent

@[expose] public section

/-! Actual original native ALL-block slabs for EVERY complete finite-prefix
strong pair, on BOTH cuts. Primitive divisibility, full coefficient descent and
the exact native quarter phase are all internal. This presents the recovered
root component; reconstruction of genuine original sources remains unpaid. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The complete ORIGINAL native denominator of one actual scheduled block. -/
def originalScheduledNativeBlockPolynomial (bound : ℕ → ℕ) (n : ℕ) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  ∏ j : Fin (originalReflectedOrderSchedule bound n),
    originalPositiveSheetPolynomial 1 ((originalScheduledParameterBlock bound n).parameter j)

/-- The native sheet dilates with the quarter phase applied only once. -/
theorem originalPositiveSheetPolynomial_native_dilation (d : ℕ) (a : ℝ) :
    originalPositiveDilation d (originalPositiveSheetPolynomial 1 a) =
      originalPositiveSheetPolynomial d a := by
  simp only [originalPositiveSheetPolynomial, map_sub, map_add,
    originalPositiveDilation_single, Nat.mul_zero, Nat.mul_one]

/-- The ENTIRE actual block is the dilation of its ENTIRE original denominator. -/
theorem originalScheduledBlockPositivePolynomial_native_dilation (bound : ℕ → ℕ)
    (k : ℕ) (i : Fin k) :
    originalScheduledBlockPositivePolynomial bound k i =
      originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
        (originalScheduledNativeBlockPolynomial bound i.val) := by
  simp only [originalScheduledBlockPositivePolynomial, originalScheduledNativeBlockPolynomial,
    map_prod, originalPositiveSheetPolynomial_native_dilation]

/-- A genuine invariant scaled block numerator has its ENTIRE original native
slab. Every exponent divisibility is derived from actual stored primitive roots. -/
theorem originalScheduledPrivateInvariant_native_slab (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (u : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hu : OriginalPositiveInSquare u (originalScheduledChartBlockDegree bound k i))
    (ht : u.coeff (originalScheduledChartBlockDegree bound k i, originalScheduledChartBlockDegree bound k i) = 0)
    (hinv : ∀ (j : Fin k), i ≠ j → ∀ g : OriginalScheduledPrimeTorus bound j.val,
      originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g) u = u) :
    ∃ r : productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ,
      u = originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
        (originalPhasedSlabPositivePolynomial (originalReflectedOrderSchedule bound i.val) r) := by
  let d := originalScheduledPrefixCoordinateDilation bound k i
  let s := originalReflectedOrderSchedule bound i.val
  have hd : 0 < d := originalScheduledPrefixCoordinateDilation_pos bound k i
  have hdiv : ∀ n ∈ u.coeff.support, d ∣ n.1 ∧ d ∣ n.2 :=
    originalScheduledPrivateInvariant_support_dilation bound k i u hinv
  let p := originalPositiveNativeDescent d u
  have hp : OriginalPositiveInSquare p s := originalPositiveNativeDescent_inSquare d s hd u hdiv hu
  have hpt : p.coeff (s, s) = 0 := originalPositiveNativeDescent_top_zero d s hd u hdiv ht
  refine ⟨originalNativePhasedSlabCoefficients s p, ?_⟩
  rw [originalPhasedSlabPositivePolynomial_reconstruct s p hp hpt]
  exact (originalPositiveNativeDescent_roundtrip d u hdiv).symm

/-- ALL actual invariant block numerators descend using the full existing
dependent native coefficient types, including the origin and all edge rows. -/
theorem originalScheduledAllBlock_native_slabs (bound : ℕ → ℕ) (k : ℕ)
    (u : Fin k → AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hu : ∀ i, OriginalPositiveInSquare (u i) (originalScheduledChartBlockDegree bound k i) ∧
      (u i).coeff (originalScheduledChartBlockDegree bound k i, originalScheduledChartBlockDegree bound k i) = 0 ∧
      ∀ (j : Fin k), i ≠ j → ∀ g : OriginalScheduledPrimeTorus bound j.val,
        originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g) (u i) = u i) :
    ∃ r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ,
      ∀ i, u i = originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
        (originalPhasedSlabPositivePolynomial (originalReflectedOrderSchedule bound i.val) (r i)) := by
  classical
  choose r hr using fun i => originalScheduledPrivateInvariant_native_slab bound k i (u i)
    (hu i).1 (hu i).2.1 (hu i).2.2
  exact ⟨r, hr⟩

/-- EVERY complete actual original positive cut has the exact native slab
numerator AND fraction sum. No support, descent or phase certificate is input. -/
theorem originalScheduledPrefixFraction_native_slabs (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ,
      originalScheduledPrefixPositiveNumerator bound k T hT =
        ∑ i : Fin k, originalScheduledOtherBlocksPolynomial bound k i *
          originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
            (originalPhasedSlabPositivePolynomial (originalReflectedOrderSchedule bound i.val) (r i)) ∧
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (originalScheduledPrefixPositiveNumerator bound k T hT) / f (originalScheduledPrefixPolynomial bound k) =
        ∑ i : Fin k,
          f (originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
            (originalPhasedSlabPositivePolynomial (originalReflectedOrderSchedule bound i.val) (r i))) /
          f (originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
            (originalScheduledNativeBlockPolynomial bound i.val)) := by
  obtain ⟨u, hu, hr⟩ := originalScheduledPrefixNumerator_all_block_split bound k T hT
  obtain ⟨r, hn⟩ := originalScheduledAllBlock_native_slabs bound k u hu
  have hn' : u = fun i => originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
      (originalPhasedSlabPositivePolynomial (originalReflectedOrderSchedule bound i.val) (r i)) := funext hn
  rw [hn'] at hr
  refine ⟨r, hr, ?_⟩
  have hf := originalScheduledAllBlock_fraction_sum bound k _ _ hr
  simpa only [originalScheduledBlockPositivePolynomial_native_dilation] using hf

/-- The strict-negative original cut has the same FULL native slab scope and
literal original sign. Its complete original pair hypothesis is unchanged. -/
theorem originalScheduledPrefixNegativeFraction_native_slabs (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ,
      -originalScheduledPrefixPositiveNumerator bound k T hT =
        ∑ i : Fin k, originalScheduledOtherBlocksPolynomial bound k i *
          originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
            (originalPhasedSlabPositivePolynomial (originalReflectedOrderSchedule bound i.val) (r i)) ∧
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (-originalScheduledPrefixPositiveNumerator bound k T hT) / f (originalScheduledPrefixPolynomial bound k) =
        ∑ i : Fin k,
          f (originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
            (originalPhasedSlabPositivePolynomial (originalReflectedOrderSchedule bound i.val) (r i))) /
          f (originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
            (originalScheduledNativeBlockPolynomial bound i.val)) := by
  obtain ⟨u, hu, hr⟩ := originalScheduledPrefixNegativeNumerator_all_block_split bound k T hT
  obtain ⟨r, hn⟩ := originalScheduledAllBlock_native_slabs bound k u hu
  have hn' : u = fun i => originalPositiveDilation (originalScheduledPrefixCoordinateDilation bound k i)
      (originalPhasedSlabPositivePolynomial (originalReflectedOrderSchedule bound i.val) (r i)) := funext hn
  rw [hn'] at hr
  refine ⟨r, hr, ?_⟩
  have hf := originalScheduledAllBlock_fraction_sum bound k _ _ hr
  simpa only [originalScheduledBlockPositivePolynomial_native_dilation] using hf

end
end MeyerGeneralProblem.StrongParity
