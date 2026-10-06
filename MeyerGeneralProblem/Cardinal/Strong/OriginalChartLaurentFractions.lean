module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalChartLocalSplitting

@[expose] public section

/-! Exact chart rational transitions in ONE genuine Laurent fraction field.
The fixed complete-degree monomial cancels from numerator and denominator.
Actual complete original pairs supply all bounds and nonzero inputs internally;
these transitions do not assume separate-pole overlap regularity or global gluing. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Exact equally bounded polynomial chart fractions become the same signed
Laurent-coordinate expression, with the degree monomial canceled internally. -/
theorem originalPositiveChartFraction_laurent (c : Bool × Bool) (d : ℕ)
    (R P : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hR : OriginalPositiveInSquare R d)
    (hP : OriginalPositiveInSquare P d) (hP0 : P ≠ 0) :
    let f := algebraMap (AddMonoidAlgebra ℂ (ℤ × ℤ)) (FractionRing (AddMonoidAlgebra ℂ (ℤ × ℤ)))
    f (originalPositiveLaurentEmbedding (originalPositiveChartReflection c d R)) /
        f (originalPositiveLaurentEmbedding (originalPositiveChartReflection c d P)) =
      f (originalLaurentChartSign c (originalPositiveLaurentEmbedding R)) /
        f (originalLaurentChartSign c (originalPositiveLaurentEmbedding P)) := by
  let f := algebraMap (AddMonoidAlgebra ℂ (ℤ × ℤ)) (FractionRing (AddMonoidAlgebra ℂ (ℤ × ℤ)))
  have hi : Function.Injective f := IsFractionRing.injective _ _
  have hL := originalPositiveLaurentEmbedding_ne_zero _ (originalPositiveChartReflection_ne_zero c d P hP hP0)
  rw [originalPositiveChartReflection_laurent c d P hP, originalLaurentChartReflection_shift] at hL
  have hf := (map_ne_zero_iff f hi).mpr hL
  rw [map_mul] at hf
  have hm0 := (mul_ne_zero_iff.mp hf).1
  have hS0 := (mul_ne_zero_iff.mp hf).2
  dsimp only
  rw [originalPositiveChartReflection_laurent c d R hR,
    originalPositiveChartReflection_laurent c d P hP,
    originalLaurentChartReflection_shift, originalLaurentChartReflection_shift, map_mul, map_mul]
  field_simp [hm0, hS0]

/-- EVERY complete actual original positive cut has its exact signed-coordinate
chart transition in the SAME genuine Laurent fraction field on ALL four charts. -/
theorem originalScheduledPrefixChartFraction_laurent (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    let f := algebraMap (AddMonoidAlgebra ℂ (ℤ × ℤ)) (FractionRing (AddMonoidAlgebra ℂ (ℤ × ℤ)))
    f (originalPositiveLaurentEmbedding (originalScheduledPrefixChartNumerator c bound k T hT)) /
        f (originalPositiveLaurentEmbedding (originalScheduledPrefixChartPolynomial c bound k)) =
      f (originalLaurentChartSign c (originalPositiveLaurentEmbedding (originalScheduledPrefixPositiveNumerator bound k T hT))) /
        f (originalLaurentChartSign c (originalPositiveLaurentEmbedding (originalScheduledPrefixPolynomial bound k))) :=
  originalPositiveChartFraction_laurent c _ _ _ (originalScheduledPrefixPositiveNumerator_inSquare bound k T hT)
    (originalScheduledPrefixPolynomial_inSquare bound k) (originalScheduledPrefixPolynomial_ne_zero bound k)

/-- The strict-negative root-component cut has the exact same actual chart
transition with its original sign; no bound/transition/nonzero certificate is supplied. -/
theorem originalScheduledPrefixNegativeChartFraction_laurent (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    let f := algebraMap (AddMonoidAlgebra ℂ (ℤ × ℤ)) (FractionRing (AddMonoidAlgebra ℂ (ℤ × ℤ)))
    f (originalPositiveLaurentEmbedding (-originalScheduledPrefixChartNumerator c bound k T hT)) /
        f (originalPositiveLaurentEmbedding (originalScheduledPrefixChartPolynomial c bound k)) =
      f (originalLaurentChartSign c (originalPositiveLaurentEmbedding (-originalScheduledPrefixPositiveNumerator bound k T hT))) /
        f (originalLaurentChartSign c (originalPositiveLaurentEmbedding (originalScheduledPrefixPolynomial bound k))) := by
  simpa only [originalScheduledPrefixChartNumerator, originalScheduledPrefixChartPolynomial, map_neg] using
    originalPositiveChartFraction_laurent c _ _ _
      (originalPositiveInSquare_neg _ _ (originalScheduledPrefixPositiveNumerator_inSquare bound k T hT))
      (originalScheduledPrefixPolynomial_inSquare bound k) (originalScheduledPrefixPolynomial_ne_zero bound k)

end
end MeyerGeneralProblem.StrongParity
