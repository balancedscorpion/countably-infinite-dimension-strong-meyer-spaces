module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalLaurentOverlapBounds

@[expose] public section

/-! Internally derived nonzero corner coefficients for actual original divisors.
The full chart orbit and literal native evaluation give the origin coefficients;
exact bounded reflection gives the top corners. The entire complement is kept. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Native evaluation at the chart origin is exactly its literal coefficient. -/
theorem originalPositiveTorusEvaluation_origin (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    originalPositiveTorusEvaluation 0 0 p = p.coeff (0, 0) := by
  refine AddMonoidAlgebra.induction_linear p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
  · intro n a
    rcases n with ⟨u, v⟩
    by_cases hu : u = 0 <;> by_cases hv : v = 0 <;>
      simp [originalPositiveTorusEvaluation_single, AddMonoidAlgebra.coeff_single, hu, hv]

/-- Every actual chart block has nonzero origin coefficient, without a supplied
corner certificate; its entire orbit and exact unit-character coefficient pay it. -/
theorem originalScheduledChartBlockPolynomial_origin_ne_zero (c : Bool × Bool)
    (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    (originalScheduledChartBlockPolynomial c bound k i).coeff (0, 0) ≠ 0 := by
  obtain ⟨g, hg⟩ := originalScheduledChartBlock_full_orbit_avoids c bound k i 0 0
  rw [originalPositiveTorusEvaluation_origin, ← originalScheduledChartBlock_character_twist,
    originalPositiveCharacterTwist_coefficient] at hg
  simpa [originalNativeIntegerEmbedding] using hg

/-- The full square bound makes the doubly reflected origin EXACTLY the original
top corner. Integer reflection is globally injective; no Nat truncation is used. -/
theorem originalPositiveChartReflection_top_coefficient (d : ℕ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : OriginalPositiveInSquare p d) :
    (originalPositiveChartReflection (true, true) d p).coeff (0, 0) = p.coeff (d, d) := by
  have h := originalPositiveChartReflection_laurent (true, true) d p hp
  have hc := Finsupp.mapDomain_apply_of_injective
    (originalChartIntegerIndex_injective (true, true) d)
    (originalPositiveLaurentEmbedding p).coeff ((d : ℤ), (d : ℤ))
  have hz : originalChartIntegerIndex (true, true) d ((d : ℤ), (d : ℤ)) = (0, 0) := by
    simp [originalChartIntegerIndex, originalChartIntegerShift, originalChartIntegerSign]
  rw [hz] at hc
  have hr : (originalPositiveLaurentEmbedding (originalPositiveChartReflection (true, true) d p)).coeff (0, 0) =
      (originalPositiveLaurentEmbedding p).coeff ((d : ℤ), (d : ℤ)) := by
    rw [h]
    exact hc
  change (originalPositiveLaurentEmbedding (originalPositiveChartReflection (true, true) d p)).coeff
      (originalNativeIntegerEmbedding (0, 0)) =
    (originalPositiveLaurentEmbedding p).coeff (originalNativeIntegerEmbedding (d, d)) at hr
  simpa only [originalPositiveLaurentEmbedding_coeff,
    originalPositivePolynomialIntegerCoefficients_apply] using hr

/-- The actual original whole block has its literal nonzero top corner. -/
theorem originalScheduledBlockPositivePolynomial_top_ne_zero (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    (originalScheduledBlockPositivePolynomial bound k i).coeff
      (originalScheduledChartBlockDegree bound k i, originalScheduledChartBlockDegree bound k i) ≠ 0 := by
  have h := originalScheduledChartBlockPolynomial_origin_ne_zero (true, true) bound k i
  change (originalPositiveChartReflection (true, true) (originalScheduledChartBlockDegree bound k i)
    (originalScheduledBlockPositivePolynomial bound k i)).coeff (0, 0) ≠ 0 at h
  rwa [originalPositiveChartReflection_top_coefficient _ _
    (originalScheduledBlockPositivePolynomial_inSquare bound k i)] at h

/-- The entire original complement uses the sum of ALL remaining block degrees. -/
def originalScheduledChartOtherDegree (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) : ℕ :=
  ∑ j ∈ Finset.univ.erase i, originalScheduledChartBlockDegree bound k j

/-- Every coefficient of the actual whole complement has its full square bound. -/
theorem originalScheduledOtherBlocksPolynomial_inSquare (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    OriginalPositiveInSquare (originalScheduledOtherBlocksPolynomial bound k i)
      (originalScheduledChartOtherDegree bound k i) :=
  originalPositiveInSquare_prod _ _ _
    (fun j _ => originalScheduledBlockPositivePolynomial_inSquare bound k j)

/-- Reflecting the entire complement at its actual sum degree gives precisely
the product of ALL reflected blocks; no certificate for the factorization. -/
theorem originalScheduledOtherBlocksPolynomial_chart (c : Bool × Bool)
    (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    originalPositiveChartReflection c (originalScheduledChartOtherDegree bound k i)
      (originalScheduledOtherBlocksPolynomial bound k i) =
      originalScheduledChartOtherBlocksPolynomial c bound k i :=
  originalPositiveChartReflection_prod c _ _ _
    (fun j _ => originalScheduledBlockPositivePolynomial_inSquare bound k j)

/-- Every actual chart complement has a nonzero origin, including the empty
complement. All original whole factors and their native phases are retained. -/
theorem originalScheduledChartOtherBlocksPolynomial_origin_ne_zero (c : Bool × Bool)
    (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    (originalScheduledChartOtherBlocksPolynomial c bound k i).coeff (0, 0) ≠ 0 := by
  classical
  rw [← originalPositiveTorusEvaluation_origin]
  simp only [originalScheduledChartOtherBlocksPolynomial, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => by
    rw [originalPositiveTorusEvaluation_origin]
    exact originalScheduledChartBlockPolynomial_origin_ne_zero c bound k j

/-- The actual original entire complement has its nonzero top corner internally. -/
theorem originalScheduledOtherBlocksPolynomial_top_ne_zero (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    (originalScheduledOtherBlocksPolynomial bound k i).coeff
      (originalScheduledChartOtherDegree bound k i, originalScheduledChartOtherDegree bound k i) ≠ 0 := by
  have h := originalScheduledChartOtherBlocksPolynomial_origin_ne_zero (true, true) bound k i
  rw [← originalScheduledOtherBlocksPolynomial_chart] at h
  rwa [originalPositiveChartReflection_top_coefficient _ _
    (originalScheduledOtherBlocksPolynomial_inSquare bound k i)] at h

end
end MeyerGeneralProblem.StrongParity
