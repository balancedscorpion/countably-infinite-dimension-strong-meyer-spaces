module

public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalMixedFractions
public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPositiveCharacters

@[expose] public section

/-! Genuine positive polynomial fraction cancellation. An invariant fraction
cannot keep a denominator factor relatively prime to its twisted denominator.
The argument uses injectivity and divisibility, without a Bezout assertion. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Exact common-complement normalization of a genuine polynomial fraction difference. -/
theorem originalPositiveFractionDifference_normalize
    (u v p q E : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : p ≠ 0) (hq : q ≠ 0) (hE : E ≠ 0) :
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f (u * p - v * q) / f (p * q * E) = f u / f (q * E) - f v / f (p * E) := by
  let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  have hp0 := (map_ne_zero_iff f hinj).mpr hp
  have hq0 := (map_ne_zero_iff f hinj).mpr hq
  have hE0 := (map_ne_zero_iff f hinj).mpr hE
  change f (u * p - v * q) / f (p * q * E) = f u / f (q * E) - f v / f (p * E)
  simp only [map_mul, map_sub]
  field_simp [hp0, hq0, hE0]

/-- Invariance forces a relatively prime twisted denominator factor to divide the actual numerator. -/
theorem originalPositiveInvariantFraction_dvd_numerator
    (χ : Multiplicative (ℤ × ℤ) →* ℂˣ) (a b p : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hb : b ≠ 0) (hp : p ∣ b) (hrel : IsRelPrime p (originalPositiveCharacterTwist χ b))
    (hinv :
      let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
      f (originalPositiveCharacterTwist χ a) / f (originalPositiveCharacterTwist χ b) = f a / f b) :
    p ∣ a := by
  let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  have hb0 := (map_ne_zero_iff f hinj).mpr hb
  have hχb0 := (map_ne_zero_iff f hinj).mpr (originalPositiveCharacterTwist_ne_zero χ b hb)
  have hc := (div_eq_div_iff hχb0 hb0).mp hinv
  have he : originalPositiveCharacterTwist χ a * b = a * originalPositiveCharacterTwist χ b := by
    apply hinj
    simpa only [map_mul] using hc
  have hd := hp.mul_left (originalPositiveCharacterTwist χ a)
  rw [he] at hd
  exact hrel.dvd_of_dvd_mul_right hd

end
end MeyerGeneralProblem.StrongParity
