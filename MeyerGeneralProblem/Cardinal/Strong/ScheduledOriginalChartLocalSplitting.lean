module

public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalLocalSplitting
public import MeyerGeneralProblem.Cardinal.Strong.OriginalChartHomogeneousEvaluation

@[expose] public section

/-! Actual finite orbit partitions and local separate-pole lifts on ALL four
charts for EVERY complete original strong pair and BOTH root-component cuts.
No unit-ideal, orbit, divisor or local-splitting certificate is supplied.
Polynomial lifts can have high degree; global compatibility and degree descent
remain separate obligations. The cone/root companion remains in the full pair. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The ENTIRE actual private-prime orbit gives a genuine finite polynomial partition
on ANY chart. All complex points, axis/infinity cases and partition coefficients
are derived internally; the original two crossing divisors need not be comaximal. -/
theorem originalScheduledChartBlock_orbit_partition (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    ∃ s : Finset (OriginalScheduledPrimeTorus bound i.val),
      ∃ w : OriginalScheduledPrimeTorus bound i.val → AddMonoidAlgebra ℂ (ℕ × ℕ),
        ∑ g ∈ s, w g * originalScheduledChartCharacterBlockPolynomial c bound k i g = 1 :=
  originalPositivePolynomialOrbit_partition_of_no_common_zero _
    (originalScheduledChartBlock_full_orbit_avoids c bound k i)

/-- EVERY complete original strong pair has actual polynomial separate-pole lifts
on EVERY chart, supplied by its original positive cut and exact orbit partition. -/
theorem originalScheduledPrefixChartNumerator_local_split (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (i : Fin k) :
    ∃ U V : AddMonoidAlgebra ℂ (ℕ × ℕ),
      originalScheduledPrefixChartNumerator c bound k T hT =
        originalScheduledChartOtherBlocksPolynomial c bound k i * U + originalScheduledChartBlockPolynomial c bound k i * V := by
  obtain ⟨s, w, hw⟩ := originalScheduledChartBlock_orbit_partition c bound k i
  exact originalPositiveLocalSplit_of_partition s w _ _ _ _ _ hw
    (fun g => originalScheduledPrefixChartComplement_dvd_difference_numerator c bound k T hT i g)

/-- The actual strict-negative cut supplies its separate-pole lifts with the exact
original sign and the same INTERNALLY derived full orbit and divisor inputs. -/
theorem originalScheduledPrefixNegativeChartNumerator_local_split (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (i : Fin k) :
    ∃ U V : AddMonoidAlgebra ℂ (ℕ × ℕ),
      -originalScheduledPrefixChartNumerator c bound k T hT =
        originalScheduledChartOtherBlocksPolynomial c bound k i * U + originalScheduledChartBlockPolynomial c bound k i * V := by
  obtain ⟨s, w, hw⟩ := originalScheduledChartBlock_orbit_partition c bound k i
  exact originalPositiveLocalSplit_of_partition s w _ _ _ _ _ hw
    (fun g => originalScheduledPrefixNegativeChartComplement_dvd_difference_numerator c bound k T hT i g)

/-- EVERY complete actual original positive cut has genuine local separate-pole
fractions using ONLY the original selected chart block and its literal complement. -/
theorem originalScheduledPrefixChartFraction_local_split (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (i : Fin k) :
    ∃ U V : AddMonoidAlgebra ℂ (ℕ × ℕ),
      originalScheduledPrefixChartNumerator c bound k T hT =
        originalScheduledChartOtherBlocksPolynomial c bound k i * U + originalScheduledChartBlockPolynomial c bound k i * V ∧
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (originalScheduledPrefixChartNumerator c bound k T hT) / f (originalScheduledPrefixChartPolynomial c bound k) =
        f U / f (originalScheduledChartBlockPolynomial c bound k i) + f V / f (originalScheduledChartOtherBlocksPolynomial c bound k i) := by
  obtain ⟨U, V, hR⟩ := originalScheduledPrefixChartNumerator_local_split c bound k T hT i
  refine ⟨U, V, hR, ?_⟩
  dsimp only
  rw [originalScheduledPrefixChartPolynomial_block_complement c bound k i]
  apply originalPositiveLocalSplit_fraction _ _ _ U V hR
  · rw [← originalScheduledChartCharacterBlockPolynomial_one]
    exact originalScheduledChartCharacterBlockPolynomial_ne_zero c bound k i _
  · exact originalScheduledChartOtherBlocksPolynomial_ne_zero c bound k i

/-- The actual strict-negative cut has the same genuine local denominator split,
without a supplied partition/divisibility certificate or a hidden global lift. -/
theorem originalScheduledPrefixNegativeChartFraction_local_split (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (i : Fin k) :
    ∃ U V : AddMonoidAlgebra ℂ (ℕ × ℕ),
      -originalScheduledPrefixChartNumerator c bound k T hT =
        originalScheduledChartOtherBlocksPolynomial c bound k i * U + originalScheduledChartBlockPolynomial c bound k i * V ∧
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (-originalScheduledPrefixChartNumerator c bound k T hT) / f (originalScheduledPrefixChartPolynomial c bound k) =
        f U / f (originalScheduledChartBlockPolynomial c bound k i) + f V / f (originalScheduledChartOtherBlocksPolynomial c bound k i) := by
  obtain ⟨U, V, hR⟩ := originalScheduledPrefixNegativeChartNumerator_local_split c bound k T hT i
  refine ⟨U, V, hR, ?_⟩
  dsimp only
  rw [originalScheduledPrefixChartPolynomial_block_complement c bound k i]
  apply originalPositiveLocalSplit_fraction _ _ _ U V hR
  · rw [← originalScheduledChartCharacterBlockPolynomial_one]
    exact originalScheduledChartCharacterBlockPolynomial_ne_zero c bound k i _
  · exact originalScheduledChartOtherBlocksPolynomial_ne_zero c bound k i

end
end MeyerGeneralProblem.StrongParity
