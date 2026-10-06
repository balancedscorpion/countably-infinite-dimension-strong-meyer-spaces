module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalPositiveIntegerCoefficients
public import Mathlib.Algebra.MonoidAlgebra.Basic

@[expose] public section

/-! The exact positive-to-Laurent algebra map for original native coefficients.
Both coordinate casts are injective; every coefficient collision is preserved. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The original coordinate embedding also preserves zero and addition. -/
def originalNativeIntegerAddHom : (ℕ × ℕ) →+ (ℤ × ℤ) where
  toFun := originalNativeIntegerEmbedding
  map_zero' := rfl
  map_add' p q := by
    change (((p.1 + q.1 : ℕ) : ℤ), ((p.2 + q.2 : ℕ) : ℤ)) =
      ((p.1 : ℤ) + (q.1 : ℤ), (p.2 : ℤ) + (q.2 : ℤ))
    simp only [Nat.cast_add]

/-- Genuine original positive-to-Laurent algebra embedding, before any division. -/
def originalPositiveLaurentEmbedding :
    AddMonoidAlgebra ℂ (ℕ × ℕ) →ₐ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ originalNativeIntegerAddHom

/-- The embedding retains the actual original integer coefficients exactly. -/
theorem originalPositiveLaurentEmbedding_coeff (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    (originalPositiveLaurentEmbedding q).coeff = originalPositivePolynomialIntegerCoefficients q := rfl

/-- Every original monomial keeps its value and both exact native coordinates. -/
theorem originalPositiveLaurentEmbedding_single (n : ℕ × ℕ) (c : ℂ) :
    originalPositiveLaurentEmbedding (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single (originalNativeIntegerEmbedding n) c := by
  exact AddMonoidAlgebra.mapDomain_single

/-- The actual whole coefficient embedding is injective, with no positivity certificate. -/
theorem originalPositiveLaurentEmbedding_injective :
    Function.Injective originalPositiveLaurentEmbedding :=
  AddMonoidAlgebra.mapDomain_injective originalNativeIntegerEmbedding.injective

/-- A nonzero genuine positive original polynomial remains nonzero in the Laurent algebra. -/
theorem originalPositiveLaurentEmbedding_ne_zero (q : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hq : q ≠ 0) : originalPositiveLaurentEmbedding q ≠ 0 := by
  intro h
  exact hq (originalPositiveLaurentEmbedding_injective (h.trans (map_zero _).symm))

end
end MeyerGeneralProblem.StrongParity
