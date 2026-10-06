module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalChartMixedIdentities

@[expose] public section

/-! EVERY complete actual original strong pair supplies its genuine numerator
and denominator on ALL four fixed projective charts. BOTH root-component cuts
retain exact signs, full support bounds and internally derived mixed equations.
The cone/root companion remains in the earlier complete decomposition. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual complete original denominator on the selected fixed-degree chart. -/
def originalScheduledPrefixChartPolynomial (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  originalPositiveChartReflection c (originalScheduledPrefixPolynomialDegree bound k)
    (originalScheduledPrefixPolynomial bound k)

/-- The actual recovered root-component numerator on the selected complete-degree chart. -/
def originalScheduledPrefixChartNumerator (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  originalPositiveChartReflection c (originalScheduledPrefixPolynomialDegree bound k)
    (originalScheduledPrefixPositiveNumerator bound k T hT)

/-- The actual complete denominator is internally nonzero on EVERY projective chart. -/
theorem originalScheduledPrefixChartPolynomial_ne_zero (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) :
    originalScheduledPrefixChartPolynomial c bound k ≠ 0 :=
  originalPositiveChartReflection_ne_zero c _ _ (originalScheduledPrefixPolynomial_inSquare bound k)
    (originalScheduledPrefixPolynomial_ne_zero bound k)

/-- The actual complete denominator retains its full original degree bound on EVERY chart. -/
theorem originalScheduledPrefixChartPolynomial_inSquare (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) :
    OriginalPositiveInSquare (originalScheduledPrefixChartPolynomial c bound k)
      (originalScheduledPrefixPolynomialDegree bound k) :=
  originalPositiveChartReflection_inSquare c _ _ (originalScheduledPrefixPolynomial_inSquare bound k)

/-- EVERY original complete pair supplies the fixed-degree chart numerator bound internally. -/
theorem originalScheduledPrefixChartNumerator_inSquare (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    OriginalPositiveInSquare (originalScheduledPrefixChartNumerator c bound k T hT)
      (originalScheduledPrefixPolynomialDegree bound k) :=
  originalPositiveChartReflection_inSquare c _ _ (originalScheduledPrefixPositiveNumerator_inSquare bound k T hT)

/-- ALL original integer rows of the actual numerator transport with exact native signed coordinates. -/
theorem originalScheduledPrefixChartNumerator_laurent (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    originalPositiveLaurentEmbedding (originalScheduledPrefixChartNumerator c bound k T hT) =
      originalLaurentChartReflection c (originalScheduledPrefixPolynomialDegree bound k)
        (originalPositiveLaurentEmbedding (originalScheduledPrefixPositiveNumerator bound k T hT)) :=
  originalPositiveChartReflection_laurent c _ _ (originalScheduledPrefixPositiveNumerator_inSquare bound k T hT)

/-- Reflection returns EVERY original positive numerator coefficient; no selected source span is substituted. -/
theorem originalScheduledPrefixChartNumerator_involutive (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    originalPositiveChartReflection c (originalScheduledPrefixPolynomialDegree bound k)
      (originalScheduledPrefixChartNumerator c bound k T hT) = originalScheduledPrefixPositiveNumerator bound k T hT :=
  originalPositiveChartReflection_involutive c _ _ (originalScheduledPrefixPositiveNumerator_inSquare bound k T hT)

/-- The original omitted top corner moves to its EXACT chart corner and remains zero. -/
theorem originalScheduledPrefixChartNumerator_missing_corner (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    (originalScheduledPrefixChartNumerator c bound k T hT).coeff
      (originalChartNativeIndex c (originalScheduledPrefixPolynomialDegree bound k)
        (originalScheduledPrefixPolynomialDegree bound k, originalScheduledPrefixPolynomialDegree bound k)) = 0 := by
  rw [originalScheduledPrefixChartNumerator, originalPositiveChartReflection_coeff_reflected c _ _
    (originalScheduledPrefixPositiveNumerator_inSquare bound k T hT) _ ⟨le_rfl, le_rfl⟩]
  by_contra hc
  have h := originalScheduledPrefixPositiveNumerator_support_box bound k T hT (Finsupp.mem_support_iff.mpr hc)
  exact h.2.2 rfl

/-- The shared coarse empty prefix retains its actual unit denominator on ALL charts. -/
theorem originalScheduledPrefixChartPolynomial_empty (c : Bool × Bool) (bound : ℕ → ℕ) :
    originalScheduledPrefixChartPolynomial c bound 0 = 1 := by
  simp only [originalScheduledPrefixChartPolynomial, originalScheduledPrefixPolynomialDegree,
    Finset.univ_eq_empty, Finset.sum_empty, originalScheduledPrefixPolynomial_zero]
  change originalPositiveChartReflection c 0 (AddMonoidAlgebra.single (0, 0) 1) = _
  rw [originalPositiveChartReflection_single]
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- EVERY complete original source on the shared coarse empty prefix has zero chart numerator. -/
theorem originalScheduledPrefixChartNumerator_empty (c : Bool × Bool) (bound : ℕ → ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound 0)) :
    originalScheduledPrefixChartNumerator c bound 0 T hT = 0 := by
  rw [originalScheduledPrefixChartNumerator, originalScheduledPrefixPositiveNumerator_empty bound T hT, map_zero]

/-- EVERY actual original positive cut supplies its WHOLE mixed equation on EVERY chart and ALL actual characters. -/
theorem originalScheduledPrefixChartNumerator_mixed_identity (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    originalPositiveMixedNumerator (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledPrimeCharacter bound j.val h) (originalScheduledPrefixChartPolynomial c bound k)
      (originalScheduledPrefixChartNumerator c bound k T hT) = 0 := by
  have hm := originalPositiveMixedNumerator_chart_eq_zero c (originalScheduledPrefixPolynomialDegree bound k)
    (originalScheduledPrimeCharacter bound i.val (originalScheduledChartPrimeTorus c bound i.val g))
    (originalScheduledPrimeCharacter bound j.val (originalScheduledChartPrimeTorus c bound j.val h)) _ _
    (originalScheduledPrefixPolynomial_inSquare bound k) (originalScheduledPrefixPositiveNumerator_inSquare bound k T hT)
    (originalScheduledPrefixPositiveNumerator_mixed_identity bound k T hT i j hij _ _)
  rw [originalScheduledChartPrimeCharacter, originalScheduledChartPrimeCharacter,
    originalScheduledChartPrimeTorus_involutive, originalScheduledChartPrimeTorus_involutive] at hm
  exact hm

/-- The actual strict negative root-component cut has the SAME chart mixed equation and exact original sign. -/
theorem originalScheduledPrefixNegativeChartNumerator_mixed_identity (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    originalPositiveMixedNumerator (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledPrimeCharacter bound j.val h) (originalScheduledPrefixChartPolynomial c bound k)
      (-originalScheduledPrefixChartNumerator c bound k T hT) = 0 := by
  have hm := originalPositiveMixedNumerator_chart_eq_zero c (originalScheduledPrefixPolynomialDegree bound k)
    (originalScheduledPrimeCharacter bound i.val (originalScheduledChartPrimeTorus c bound i.val g))
    (originalScheduledPrimeCharacter bound j.val (originalScheduledChartPrimeTorus c bound j.val h)) _ _
    (originalScheduledPrefixPolynomial_inSquare bound k)
    (originalPositiveInSquare_neg _ _ (originalScheduledPrefixPositiveNumerator_inSquare bound k T hT))
    (originalScheduledPrefixNegativePositiveNumerator_mixed_identity bound k T hT i j hij _ _)
  rw [originalScheduledChartPrimeCharacter, originalScheduledChartPrimeCharacter,
    originalScheduledChartPrimeTorus_involutive, originalScheduledChartPrimeTorus_involutive, map_neg] at hm
  exact hm

/-- Actual positive chart fractions obey the genuine field identity with all four nonzero denominators internal. -/
theorem originalScheduledPrefixChartMixedFractions_eq_zero (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    let χ := originalScheduledPrimeCharacter bound i.val g
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let P := originalScheduledPrefixChartPolynomial c bound k
    let R := originalScheduledPrefixChartNumerator c bound k T hT
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist (χ * ψ) R) / f (originalPositiveCharacterTwist (χ * ψ) P) -
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ P) -
      f (originalPositiveCharacterTwist ψ R) / f (originalPositiveCharacterTwist ψ P) + f R / f P = 0 :=
  originalPositiveMixedFractions_eq_zero _ _ _ _ (originalScheduledPrefixChartPolynomial_ne_zero c bound k)
    (originalScheduledPrefixChartNumerator_mixed_identity c bound k T hT i j hij g h)

/-- The strict negative chart fractions obey the same genuine field equation with their exact original sign. -/
theorem originalScheduledPrefixNegativeChartMixedFractions_eq_zero (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    let χ := originalScheduledPrimeCharacter bound i.val g
    let ψ := originalScheduledPrimeCharacter bound j.val h
    let P := originalScheduledPrefixChartPolynomial c bound k
    let R := -originalScheduledPrefixChartNumerator c bound k T hT
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (originalPositiveCharacterTwist (χ * ψ) R) / f (originalPositiveCharacterTwist (χ * ψ) P) -
      f (originalPositiveCharacterTwist χ R) / f (originalPositiveCharacterTwist χ P) -
      f (originalPositiveCharacterTwist ψ R) / f (originalPositiveCharacterTwist ψ P) + f R / f P = 0 :=
  originalPositiveMixedFractions_eq_zero _ _ _ _ (originalScheduledPrefixChartPolynomial_ne_zero c bound k)
    (originalScheduledPrefixNegativeChartNumerator_mixed_identity c bound k T hT i j hij g h)

end
end MeyerGeneralProblem.StrongParity
