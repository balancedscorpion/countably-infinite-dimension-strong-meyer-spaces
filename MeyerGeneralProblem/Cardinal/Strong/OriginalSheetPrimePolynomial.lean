module

public import MeyerGeneralProblem.Cardinal.Strong.SheetEisenstein
public import MeyerGeneralProblem.Cardinal.Strong.OriginalHomogeneousPolynomial
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

/-! Exact transport of genuine native sheet coefficients to iterated polynomials.
Irreducibility and primality descend to the original coefficient algebra,
including its literal quarter phase and arbitrary nonzero translated phases. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open Polynomial

/-- Exact polynomial equivalence with Z outside and W in the coefficient ring. -/
def originalPositiveIteratedEquiv :
    AddMonoidAlgebra ℂ (ℕ × ℕ) ≃ₐ[ℂ] Polynomial ℂ[X] :=
  (AddMonoidAlgebra.curryAlgEquiv ℂ).trans
    ((AddMonoidAlgebra.mapAlgEquiv ℂ ℕ (Polynomial.toFinsuppIsoAlg ℂ).symm).trans
      ((Polynomial.toFinsuppIsoAlg ℂ[X]).symm.restrictScalars ℂ))

/-- The genuine original positive coefficient algebra inherits unique factorization. -/
instance originalPositivePolynomial_uniqueFactorization :
    UniqueFactorizationMonoid (AddMonoidAlgebra ℂ (ℕ × ℕ)) :=
  originalPositiveIteratedEquiv.symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

/-- Exact single-coefficient transport, with both coordinate indices retained. -/
theorem originalPositiveIteratedEquiv_single (n : ℕ × ℕ) (c : ℂ) :
    originalPositiveIteratedEquiv (AddMonoidAlgebra.single n c) =
      monomial n.1 (monomial n.2 c) := by
  rcases n with ⟨m, n⟩
  simp only [originalPositiveIteratedEquiv, AlgEquiv.trans_apply,
    AddMonoidAlgebra.curryAlgEquiv_single]
  change Polynomial.ofFinsupp (AddMonoidAlgebra.mapAlgHom ℕ
    ((Polynomial.toFinsuppIsoAlg ℂ).symm : AddMonoidAlgebra ℂ ℕ →ₐ[ℂ] ℂ[X])
      (AddMonoidAlgebra.single m (AddMonoidAlgebra.single n c))) = _
  rw [AddMonoidAlgebra.mapAlgHom_single]
  change Polynomial.ofFinsupp (AddMonoidAlgebra.single m
    (Polynomial.ofFinsupp (AddMonoidAlgebra.single n c))) = _
  rw [Polynomial.ofFinsupp_single, Polynomial.ofFinsupp_single]

/-- The literal native sheet under independent nonzero phases, before evaluation. -/
def originalPhasedPositiveSheetPolynomial (d : ℕ) (a : ℝ) (ρ σ : ℂ) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  AddMonoidAlgebra.single (0, 0) 1 -
    AddMonoidAlgebra.single (0, d) ((a : ℂ) * σ) +
    AddMonoidAlgebra.single (d, 0) ((a : ℂ) * ρ) -
    AddMonoidAlgebra.single (d, d) (ρ * σ)

/-- The phased sheet is exactly the genuine polynomial used by Eisenstein. -/
theorem originalPositiveIteratedEquiv_phased_sheet (d : ℕ) (a : ℝ) (ρ σ : ℂ) :
    originalPositiveIteratedEquiv (originalPhasedPositiveSheetPolynomial d a ρ σ) =
      originalSheetIteratedPolynomial d (a : ℂ) ρ σ := by
  simp only [originalPhasedPositiveSheetPolynomial, map_sub, map_add,
    originalPositiveIteratedEquiv_single, monomial_zero_left,
    ← C_mul_X_pow_eq_monomial, map_mul]
  simp only [originalSheetIteratedPolynomial, originalSheetLeadingCoefficient,
    originalSheetConstantCoefficient, map_mul, map_sub, map_one, pow_zero, mul_one]
  ring

/-- The original quarter phase is inserted after the native W power exactly once. -/
theorem originalPhasedPositiveSheetPolynomial_original (d : ℕ) (a : ℝ) :
    originalPhasedPositiveSheetPolynomial d a 1 (complexUnitPhase (-1 / 4)) =
      originalPositiveSheetPolynomial d a := by
  simp [originalPhasedPositiveSheetPolynomial, originalPositiveSheetPolynomial]

/-- Every phased sheet evaluates to its exact original four-term polynomial. -/
theorem originalPhasedPositiveSheetPolynomial_eval (d : ℕ) (a : ℝ) (ρ σ Z W : ℂ) :
    originalPositiveTorusEvaluation Z W (originalPhasedPositiveSheetPolynomial d a ρ σ) =
      sheetPolynomial (a : ℂ) (ρ * Z ^ d) (σ * W ^ d) := by
  simp only [originalPhasedPositiveSheetPolynomial, map_sub, map_add,
    originalPositiveTorusEvaluation_single, pow_zero, one_mul, mul_one]
  unfold sheetPolynomial
  ring

/-- Actual real parameter bounds exclude both coefficient degeneracies internally. -/
theorem originalSheetParameter_nondegenerate (a : ℝ) (ha : 0 < a ∧ a < 1) :
    (a : ℂ) ≠ 0 ∧ (a : ℂ) ^ 2 ≠ 1 := by
  constructor
  · exact_mod_cast ne_of_gt ha.1
  · intro he
    have hr := congrArg Complex.re he
    simp only [Complex.mul_re, pow_two, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, mul_zero, sub_zero] at hr
    nlinarith [ha.1, ha.2]

/-- Every genuine positive native sheet is irreducible with arbitrary nonzero phases. -/
theorem originalPhasedPositiveSheetPolynomial_irreducible (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ha : 0 < a ∧ a < 1) (ρ σ : ℂ) (hρ : ρ ≠ 0) (hσ : σ ≠ 0) :
    Irreducible (originalPhasedPositiveSheetPolynomial d a ρ σ) := by
  rw [← MulEquiv.irreducible_iff originalPositiveIteratedEquiv,
    originalPositiveIteratedEquiv_phased_sheet]
  exact originalSheetIteratedPolynomial_irreducible d hd (a : ℂ) ρ σ
    (originalSheetParameter_nondegenerate a ha).1
    (originalSheetParameter_nondegenerate a ha).2 hρ hσ

/-- Every genuine positive native sheet is prime in the original coefficient algebra. -/
theorem originalPhasedPositiveSheetPolynomial_prime (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ha : 0 < a ∧ a < 1) (ρ σ : ℂ) (hρ : ρ ≠ 0) (hσ : σ ≠ 0) :
    Prime (originalPhasedPositiveSheetPolynomial d a ρ σ) := by
  rw [← MulEquiv.prime_iff originalPositiveIteratedEquiv,
    originalPositiveIteratedEquiv_phased_sheet]
  exact (originalSheetIteratedPolynomial_irreducible d hd (a : ℂ) ρ σ
    (originalSheetParameter_nondegenerate a ha).1
    (originalSheetParameter_nondegenerate a ha).2 hρ hσ).prime

/-- The actual original quarter-phase native sheet is irreducible without a certificate. -/
theorem originalPositiveSheetPolynomial_irreducible (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ha : 0 < a ∧ a < 1) : Irreducible (originalPositiveSheetPolynomial d a) := by
  rw [← originalPhasedPositiveSheetPolynomial_original]
  exact originalPhasedPositiveSheetPolynomial_irreducible d hd a ha 1 _
    one_ne_zero originalQuarterPhase_ne_zero

/-- The actual original quarter-phase native sheet is prime without a certificate. -/
theorem originalPositiveSheetPolynomial_prime (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ha : 0 < a ∧ a < 1) : Prime (originalPositiveSheetPolynomial d a) := by
  rw [← originalPhasedPositiveSheetPolynomial_original]
  exact originalPhasedPositiveSheetPolynomial_prime d hd a ha 1 _
    one_ne_zero originalQuarterPhase_ne_zero

end
end MeyerGeneralProblem.StrongParity
