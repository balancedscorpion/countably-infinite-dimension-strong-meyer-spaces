module

public import MeyerGeneralProblem.Cardinal.Strong.LaurentArrayAlgebraAction
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

@[expose] public section

/-! Genuine mixed character identities for finite original Laurent numerators,
proved before division by clearing the actual four denominators. No divisor
coprimality, sparse rational decomposition or pole classification is asserted. -/
namespace MeyerGeneralProblem
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- Literal mixed differences of a character-weighted WHOLE array vanish exactly. -/
theorem originalCharacterArrayTwist_mixed_zero (χ ψ : Multiplicative G →* ℂˣ) (u : G → ℂ)
    (hu : ∀ n, ((χ (Multiplicative.ofAdd n) : ℂ) - 1) *
      ((ψ (Multiplicative.ofAdd n) : ℂ) - 1) * u n = 0) :
    originalCharacterArrayTwist (χ * ψ) u - originalCharacterArrayTwist χ u -
      originalCharacterArrayTwist ψ u + u = 0 := by
  funext n
  simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, originalCharacterArrayTwist,
    MonoidHom.mul_apply, Units.val_mul]
  linear_combination hu n

/-- The finite numerator's actual character twist represents the correspondingly
weighted original array with its correspondingly twisted denominator. -/
theorem originalLaurentNumerator_characterTwist (χ : Multiplicative G →* ℂˣ)
    (p R : AddMonoidAlgebra ℂ G) (u : G → ℂ)
    (hR : ∀ n, R.coeff n = annihilatorArrayConvolution p.coeff u n) (n : G) :
    (originalLaurentCharacterTwist χ R).coeff n =
      annihilatorArrayConvolution (originalLaurentCharacterTwist χ p).coeff
        (originalCharacterArrayTwist χ u) n := by
  rw [originalLaurentCharacterTwist_coefficient, hR, annihilatorArrayConvolution_characterTwist]

/-- Multiplying a genuine finite numerator by any Laurent factor supplies exactly
its enlarged denominator action on EVERY original array label. -/
theorem originalLaurentNumerator_mul_coefficient (a p R : AddMonoidAlgebra ℂ G) (u : G → ℂ)
    (hR : ∀ n, R.coeff n = annihilatorArrayConvolution p.coeff u n) (n : G) :
    (a * R).coeff n = annihilatorArrayConvolution (a * p).coeff u n := by
  rw [← annihilatorArrayConvolution_finite]
  have he : (fun m => R.coeff m) = annihilatorArrayConvolution p.coeff u := funext hR
  rw [he, ← annihilatorArrayConvolution_mul]

/-- The exact four-denominator polynomial, retaining every original coefficient collision. -/
def originalLaurentMixedNumerator (χ ψ : Multiplicative G →* ℂˣ)
    (p R : AddMonoidAlgebra ℂ G) : AddMonoidAlgebra ℂ G :=
  (p * originalLaurentCharacterTwist χ p * originalLaurentCharacterTwist ψ p) *
      originalLaurentCharacterTwist (χ * ψ) R -
    (p * originalLaurentCharacterTwist ψ p * originalLaurentCharacterTwist (χ * ψ) p) *
      originalLaurentCharacterTwist χ R -
    (p * originalLaurentCharacterTwist χ p * originalLaurentCharacterTwist (χ * ψ) p) *
      originalLaurentCharacterTwist ψ R +
    (originalLaurentCharacterTwist χ p * originalLaurentCharacterTwist ψ p *
      originalLaurentCharacterTwist (χ * ψ) p) * R

/-- The GENUINE mixed rational character identity, before division. Its assumptions
are the literal all-label numerator formula and mixed original array equation. -/
theorem originalLaurentMixedNumerator_eq_zero (χ ψ : Multiplicative G →* ℂˣ)
    (p R : AddMonoidAlgebra ℂ G) (u : G → ℂ)
    (hR : ∀ n, R.coeff n = annihilatorArrayConvolution p.coeff u n)
    (hu : ∀ n, ((χ (Multiplicative.ofAdd n) : ℂ) - 1) *
      ((ψ (Multiplicative.ofAdd n) : ℂ) - 1) * u n = 0) :
    originalLaurentMixedNumerator χ ψ p R = 0 := by
  let D := p * originalLaurentCharacterTwist χ p * originalLaurentCharacterTwist ψ p *
    originalLaurentCharacterTwist (χ * ψ) p
  have hmix := originalCharacterArrayTwist_mixed_zero χ ψ u hu
  ext n
  have hz := congrArg (fun v : G → ℂ => annihilatorArrayConvolution D.coeff v n) hmix
  simp only [annihilatorArrayConvolution_add, annihilatorArrayConvolution_sub,
    annihilatorArrayConvolution_zero] at hz
  simp only [originalLaurentMixedNumerator, AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_zero, Finsupp.add_apply,
    Finsupp.sub_apply, Finsupp.zero_apply]
  rw [originalLaurentNumerator_mul_coefficient _ _ _ _
      (originalLaurentNumerator_characterTwist (χ * ψ) p R u hR),
    originalLaurentNumerator_mul_coefficient _ _ _ _
      (originalLaurentNumerator_characterTwist χ p R u hR),
    originalLaurentNumerator_mul_coefficient _ _ _ _
      (originalLaurentNumerator_characterTwist ψ p R u hR),
    originalLaurentNumerator_mul_coefficient _ _ _ _ hR]
  have hχ : (p * originalLaurentCharacterTwist ψ p * originalLaurentCharacterTwist (χ * ψ) p) *
      originalLaurentCharacterTwist χ p = D := by dsimp [D]; ring
  have hψ : (p * originalLaurentCharacterTwist χ p * originalLaurentCharacterTwist (χ * ψ) p) *
      originalLaurentCharacterTwist ψ p = D := by dsimp [D]; ring
  have hid : (originalLaurentCharacterTwist χ p * originalLaurentCharacterTwist ψ p *
      originalLaurentCharacterTwist (χ * ψ) p) * p = D := by dsimp [D]; ring
  rw [hχ, hψ, hid]
  exact hz

/-- All FOUR actual denominators remain nonzero; clearing is never a zero-product shortcut. -/
theorem originalLaurentMixedDenominator_ne_zero [UniqueSums G] (χ ψ : Multiplicative G →* ℂˣ)
    (p : AddMonoidAlgebra ℂ G) (hp : p ≠ 0) :
    p * originalLaurentCharacterTwist χ p * originalLaurentCharacterTwist ψ p *
      originalLaurentCharacterTwist (χ * ψ) p ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hp (originalLaurentCharacterTwist_ne_zero χ p hp))
    (originalLaurentCharacterTwist_ne_zero ψ p hp))
    (originalLaurentCharacterTwist_ne_zero (χ * ψ) p hp)

end
end MeyerGeneralProblem
