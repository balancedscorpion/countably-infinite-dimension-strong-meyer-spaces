module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalChartCharacters

@[expose] public section

/-! The WHOLE original fraction-free mixed identity transports to every fixed
projective chart. All four terms have the same full degree scalar, which is
internally nonzero for genuine unit characters. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Four genuine polynomial factors reflect at exactly the sum of their full native square bounds. -/
theorem originalPositiveChartReflection_mul_four (c : Bool × Bool) (d : ℕ)
    (a b p q : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (ha : OriginalPositiveInSquare a d) (hb : OriginalPositiveInSquare b d)
    (hp : OriginalPositiveInSquare p d) (hq : OriginalPositiveInSquare q d) :
    originalPositiveChartReflection c (d + d + d + d) (a * b * p * q) =
      originalPositiveChartReflection c d a * originalPositiveChartReflection c d b *
        originalPositiveChartReflection c d p * originalPositiveChartReflection c d q := by
  rw [originalPositiveChartReflection_mul c (d + d + d) d (a * b * p) q
    (originalPositiveInSquare_mul (a * b) p (d + d) d
      (originalPositiveInSquare_mul a b d d ha hb) hp) hq,
    originalPositiveChartReflection_mul c (d + d) d (a * b) p
      (originalPositiveInSquare_mul a b d d ha hb) hp,
    originalPositiveChartReflection_mul c d d a b ha hb]

/-- Exact fixed-chart reflection of the COMPLETE mixed numerator, with every scalar and coefficient retained. -/
theorem originalPositiveMixedNumerator_chart_reflection (c : Bool × Bool) (d : ℕ)
    (χ ψ : Multiplicative (ℤ × ℤ) →* ℂˣ) (p R : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hp : OriginalPositiveInSquare p d) (hR : OriginalPositiveInSquare R d) :
    originalPositiveChartReflection c (d + d + d + d) (originalPositiveMixedNumerator χ ψ p R) =
      ((χ (Multiplicative.ofAdd (originalChartIntegerShift c d)) : ℂ) *
        (ψ (Multiplicative.ofAdd (originalChartIntegerShift c d)) : ℂ) *
        ((χ * ψ) (Multiplicative.ofAdd (originalChartIntegerShift c d)) : ℂ)) •
      originalPositiveMixedNumerator (originalChartCharacter c χ) (originalChartCharacter c ψ)
        (originalPositiveChartReflection c d p) (originalPositiveChartReflection c d R) := by
  have hχp := originalPositiveInSquare_twist χ p d hp
  have hψp := originalPositiveInSquare_twist ψ p d hp
  have hχψp := originalPositiveInSquare_twist (χ * ψ) p d hp
  have hχR := originalPositiveInSquare_twist χ R d hR
  have hψR := originalPositiveInSquare_twist ψ R d hR
  have hχψR := originalPositiveInSquare_twist (χ * ψ) R d hR
  simp only [originalPositiveMixedNumerator, map_add, map_sub]
  rw [originalPositiveChartReflection_mul_four c d p _ _ _ hp hχp hψp hχψR,
    originalPositiveChartReflection_mul_four c d p _ _ _ hp hψp hχψp hχR,
    originalPositiveChartReflection_mul_four c d p _ _ _ hp hχp hχψp hψR,
    originalPositiveChartReflection_mul_four c d _ _ _ R hχp hψp hχψp hR]
  rw [originalPositiveChartReflection_twist c d χ p hp,
    originalPositiveChartReflection_twist c d ψ p hp,
    originalPositiveChartReflection_twist c d (χ * ψ) p hp,
    originalPositiveChartReflection_twist c d χ R hR,
    originalPositiveChartReflection_twist c d ψ R hR,
    originalPositiveChartReflection_twist c d (χ * ψ) R hR,
    originalChartCharacter_mul]
  simp only [Algebra.smul_def, map_mul]
  ring

/-- Genuine unit characters and the actual full square transport zero mixed equations without an input scalar certificate. -/
theorem originalPositiveMixedNumerator_chart_eq_zero (c : Bool × Bool) (d : ℕ)
    (χ ψ : Multiplicative (ℤ × ℤ) →* ℂˣ) (p R : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hp : OriginalPositiveInSquare p d) (hR : OriginalPositiveInSquare R d)
    (hm : originalPositiveMixedNumerator χ ψ p R = 0) :
    originalPositiveMixedNumerator (originalChartCharacter c χ) (originalChartCharacter c ψ)
      (originalPositiveChartReflection c d p) (originalPositiveChartReflection c d R) = 0 := by
  have h := congrArg (originalPositiveChartReflection c (d + d + d + d)) hm
  rw [originalPositiveMixedNumerator_chart_reflection c d χ ψ p R hp hR, map_zero] at h
  exact (smul_eq_zero.mp h).resolve_left
    (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (Units.ne_zero _))

end
end MeyerGeneralProblem.StrongParity
