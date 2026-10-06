module

public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalLaurentEmbedding
public import MeyerGeneralProblem.Cardinal.Strong.LaurentCharacterTwists

@[expose] public section

/-! Exact restriction of genuine integer unit characters to the original positive
coefficient algebra. The action commutes with the injective Laurent embedding,
so all native phase substitutions and polynomial identities transfer exactly. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual integer unit character restricted to original positive labels. -/
def originalPositiveCharacterMonomial (χ : Multiplicative (ℤ × ℤ) →* ℂˣ) :
    Multiplicative (ℕ × ℕ) →* AddMonoidAlgebra ℂ (ℕ × ℕ) where
  toFun n := AddMonoidAlgebra.single n.toAdd (χ (Multiplicative.ofAdd (originalNativeIntegerEmbedding n.toAdd)) : ℂ)
  map_one' := by
    change AddMonoidAlgebra.single (0, 0) (χ 1 : ℂ) = 1
    rw [map_one, Units.val_one]
    rfl
  map_mul' n m := by
    have hcast : originalNativeIntegerEmbedding (n.toAdd + m.toAdd) =
        originalNativeIntegerEmbedding n.toAdd + originalNativeIntegerEmbedding m.toAdd :=
      originalNativeIntegerAddHom.map_add _ _
    change AddMonoidAlgebra.single (n.toAdd + m.toAdd)
      (χ (Multiplicative.ofAdd (originalNativeIntegerEmbedding (n.toAdd + m.toAdd))) : ℂ) =
      AddMonoidAlgebra.single n.toAdd (χ (Multiplicative.ofAdd (originalNativeIntegerEmbedding n.toAdd)) : ℂ) *
      AddMonoidAlgebra.single m.toAdd (χ (Multiplicative.ofAdd (originalNativeIntegerEmbedding m.toAdd)) : ℂ)
    rw [hcast, AddMonoidAlgebra.single_mul_single]
    change AddMonoidAlgebra.single (n.toAdd + m.toAdd)
      (χ (Multiplicative.ofAdd (originalNativeIntegerEmbedding n.toAdd) *
        Multiplicative.ofAdd (originalNativeIntegerEmbedding m.toAdd)) : ℂ) = _
    rw [map_mul, Units.val_mul]

/-- Genuine positive native character algebra homomorphism, before evaluation or division. -/
def originalPositiveCharacterTwist (χ : Multiplicative (ℤ × ℤ) →* ℂˣ) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) →ₐ[ℂ] AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  AddMonoidAlgebra.lift ℂ (AddMonoidAlgebra ℂ (ℕ × ℕ)) (ℕ × ℕ) (originalPositiveCharacterMonomial χ)

/-- Every original positive monomial is multiplied by its exact integer-character value once. -/
theorem originalPositiveCharacterTwist_single (χ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (n : ℕ × ℕ) (c : ℂ) :
    originalPositiveCharacterTwist χ (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single n ((χ (Multiplicative.ofAdd (originalNativeIntegerEmbedding n)) : ℂ) * c) := by
  classical
  rw [originalPositiveCharacterTwist, AddMonoidAlgebra.lift_single]
  change c • AddMonoidAlgebra.single n (χ (Multiplicative.ofAdd (originalNativeIntegerEmbedding n)) : ℂ) = _
  ext z
  simp only [AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.single_apply]
  split_ifs <;> ring

/-- The exact positive action commutes with the actual whole Laurent coefficient embedding. -/
theorem originalPositiveCharacterTwist_laurent (χ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    originalPositiveLaurentEmbedding (originalPositiveCharacterTwist χ q) =
      originalLaurentCharacterTwist χ (originalPositiveLaurentEmbedding q) := by
  refine AddMonoidAlgebra.induction_linear q ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro n c
    rw [originalPositiveCharacterTwist_single, originalPositiveLaurentEmbedding_single,
      originalPositiveLaurentEmbedding_single, originalLaurentCharacterTwist_single]

/-- Every whole positive coefficient receives its exact unit-character value. -/
theorem originalPositiveCharacterTwist_coefficient (χ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) (n : ℕ × ℕ) :
    (originalPositiveCharacterTwist χ q).coeff n =
      (χ (Multiplicative.ofAdd (originalNativeIntegerEmbedding n)) : ℂ) * q.coeff n := by
  have hc := congrArg (fun p : AddMonoidAlgebra ℂ (ℤ × ℤ) => p.coeff (originalNativeIntegerEmbedding n))
    (originalPositiveCharacterTwist_laurent χ q)
  simpa only [originalPositiveLaurentEmbedding_coeff, originalPositivePolynomialIntegerCoefficients_apply,
    originalLaurentCharacterTwist_coefficient] using hc

/-- Actual unit characters preserve every nonzero genuine positive polynomial. -/
theorem originalPositiveCharacterTwist_injective (χ : Multiplicative (ℤ × ℤ) →* ℂˣ) :
    Function.Injective (originalPositiveCharacterTwist χ) := by
  intro p q h
  apply originalPositiveLaurentEmbedding_injective
  apply originalLaurentCharacterTwist_injective χ
  rw [← originalPositiveCharacterTwist_laurent, ← originalPositiveCharacterTwist_laurent, h]

/-- No nonzero original positive denominator is erased by a genuine unit-character action. -/
theorem originalPositiveCharacterTwist_ne_zero (χ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : p ≠ 0) : originalPositiveCharacterTwist χ p ≠ 0 := by
  intro h
  exact hp (originalPositiveCharacterTwist_injective χ (h.trans (map_zero _).symm))

/-- Integer-character products induce commuting exact native positive actions. -/
theorem originalPositiveCharacterTwist_mul (χ ψ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    originalPositiveCharacterTwist (χ * ψ) p =
      originalPositiveCharacterTwist χ (originalPositiveCharacterTwist ψ p) := by
  apply originalPositiveLaurentEmbedding_injective
  rw [originalPositiveCharacterTwist_laurent, originalPositiveCharacterTwist_laurent,
    originalPositiveCharacterTwist_laurent, originalLaurentCharacterTwist_mul]

end
end MeyerGeneralProblem.StrongParity
