module

public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalGlobalSplitting

@[expose] public section

/-! Actual global separate-pole splitting for EVERY complete original finite
prefix strong pair and BOTH root-component cuts. All local lifts, divisor facts,
nonzero corners, overlap regularity, actual cocycle, gluing and individual degree
bounds are derived internally. The cone/root companion remains in the full pair;
private invariance, native exponent descent and source classification are unpaid. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual selected whole-block and ENTIRE complement degrees add to the
complete original prefix degree, with no omitted sheet or degree certificate. -/
theorem originalScheduledChartDegrees_sum (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    originalScheduledChartBlockDegree bound k i + originalScheduledChartOtherDegree bound k i =
      originalScheduledPrefixPolynomialDegree bound k := by
  classical
  exact Finset.add_sum_erase Finset.univ
    (fun j : Fin k => originalScheduledChartBlockDegree bound k j) (Finset.mem_univ i)

/-- EVERY actual complete original strong pair has genuine global separate-pole
positive numerators with the correct individual block and complement boxes.
No local-lift, compatibility, regularity, cocycle, gluing or degree input survives. -/
theorem originalScheduledPrefixNumerator_global_split (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (i : Fin k) :
    ∃ U V : AddMonoidAlgebra ℂ (ℕ × ℕ),
      OriginalPositiveInSquare U (originalScheduledChartBlockDegree bound k i) ∧
      OriginalPositiveInSquare V (originalScheduledChartOtherDegree bound k i) ∧
      originalScheduledPrefixPositiveNumerator bound k T hT =
        originalScheduledOtherBlocksPolynomial bound k i * U + originalScheduledBlockPositivePolynomial bound k i * V := by
  apply originalPositive_four_chart_global_split
    (originalScheduledChartBlockDegree bound k i) (originalScheduledChartOtherDegree bound k i)
    (originalScheduledBlockPositivePolynomial bound k i) (originalScheduledOtherBlocksPolynomial bound k i)
    (originalScheduledPrefixPositiveNumerator bound k T hT)
    (originalScheduledBlockPositivePolynomial_inSquare bound k i)
    (originalScheduledOtherBlocksPolynomial_inSquare bound k i)
  · rw [originalScheduledChartDegrees_sum]
    exact originalScheduledPrefixPositiveNumerator_inSquare bound k T hT
  · simpa only [originalScheduledChartBlockPolynomial, originalPositiveChartReflection_affine] using
      originalScheduledChartBlockPolynomial_origin_ne_zero (false, false) bound k i
  · exact originalScheduledBlockPositivePolynomial_top_ne_zero bound k i
  · simpa only [originalScheduledCharacterBlockPolynomial_one] using
      originalScheduledCharacterBlock_complement_isRelPrime bound k i (originalScheduledPrimeTorusIdentity bound i.val)
  · intro c
    simpa only [originalScheduledChartDegrees_sum, originalScheduledOtherBlocksPolynomial_chart,
      originalScheduledChartBlockPolynomial, originalScheduledPrefixChartNumerator] using
      originalScheduledPrefixChartNumerator_local_split c bound k T hT i

/-- The literal strict-negative root-component cut has the SAME genuine global
separate-pole bounds and exact original sign, for every actual complete pair. -/
theorem originalScheduledPrefixNegativeNumerator_global_split (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (i : Fin k) :
    ∃ U V : AddMonoidAlgebra ℂ (ℕ × ℕ),
      OriginalPositiveInSquare U (originalScheduledChartBlockDegree bound k i) ∧
      OriginalPositiveInSquare V (originalScheduledChartOtherDegree bound k i) ∧
      -originalScheduledPrefixPositiveNumerator bound k T hT =
        originalScheduledOtherBlocksPolynomial bound k i * U + originalScheduledBlockPositivePolynomial bound k i * V := by
  obtain ⟨U, V, hU, hV, hR⟩ := originalScheduledPrefixNumerator_global_split bound k T hT i
  refine ⟨-U, -V, originalPositiveInSquare_neg _ _ hU, originalPositiveInSquare_neg _ _ hV, ?_⟩
  rw [hR]
  ring

/-- EVERY actual positive cut has its genuine globally bounded separate-pole
fractions, with ONLY the original selected block and its ENTIRE complement. -/
theorem originalScheduledPrefixFraction_global_split (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (i : Fin k) :
    ∃ U V : AddMonoidAlgebra ℂ (ℕ × ℕ),
      OriginalPositiveInSquare U (originalScheduledChartBlockDegree bound k i) ∧
      OriginalPositiveInSquare V (originalScheduledChartOtherDegree bound k i) ∧
      originalScheduledPrefixPositiveNumerator bound k T hT =
        originalScheduledOtherBlocksPolynomial bound k i * U + originalScheduledBlockPositivePolynomial bound k i * V ∧
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (originalScheduledPrefixPositiveNumerator bound k T hT) / f (originalScheduledPrefixPolynomial bound k) =
        f U / f (originalScheduledBlockPositivePolynomial bound k i) + f V / f (originalScheduledOtherBlocksPolynomial bound k i) := by
  obtain ⟨U, V, hU, hV, hR⟩ := originalScheduledPrefixNumerator_global_split bound k T hT i
  refine ⟨U, V, hU, hV, hR, ?_⟩
  dsimp only
  rw [originalScheduledPrefixPolynomial_block_complement]
  apply originalPositiveLocalSplit_fraction _ _ _ U V hR
  · rw [← originalScheduledCharacterBlockPolynomial_one]
    exact originalScheduledCharacterBlockPolynomial_ne_zero bound k i _
  · exact originalScheduledOtherBlocksPolynomial_ne_zero bound k i

/-- The actual strict-negative cut has the exact same GLOBAL fraction split and
full boxes, without assuming its source belongs to the selected mode span. -/
theorem originalScheduledPrefixNegativeFraction_global_split (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (i : Fin k) :
    ∃ U V : AddMonoidAlgebra ℂ (ℕ × ℕ),
      OriginalPositiveInSquare U (originalScheduledChartBlockDegree bound k i) ∧
      OriginalPositiveInSquare V (originalScheduledChartOtherDegree bound k i) ∧
      -originalScheduledPrefixPositiveNumerator bound k T hT =
        originalScheduledOtherBlocksPolynomial bound k i * U + originalScheduledBlockPositivePolynomial bound k i * V ∧
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (-originalScheduledPrefixPositiveNumerator bound k T hT) / f (originalScheduledPrefixPolynomial bound k) =
        f U / f (originalScheduledBlockPositivePolynomial bound k i) + f V / f (originalScheduledOtherBlocksPolynomial bound k i) := by
  obtain ⟨U, V, hU, hV, hR⟩ := originalScheduledPrefixNegativeNumerator_global_split bound k T hT i
  refine ⟨U, V, hU, hV, hR, ?_⟩
  dsimp only
  rw [originalScheduledPrefixPolynomial_block_complement]
  apply originalPositiveLocalSplit_fraction _ _ _ U V hR
  · rw [← originalScheduledCharacterBlockPolynomial_one]
    exact originalScheduledCharacterBlockPolynomial_ne_zero bound k i _
  · exact originalScheduledOtherBlocksPolynomial_ne_zero bound k i

end
end MeyerGeneralProblem.StrongParity
