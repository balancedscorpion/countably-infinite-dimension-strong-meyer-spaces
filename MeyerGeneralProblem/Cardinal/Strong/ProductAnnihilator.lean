module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalPairNumerator
public import MeyerGeneralProblem.Cardinal.Strong.SheetProducts
public import Mathlib.Algebra.MonoidAlgebra.Basic

@[expose] public section

/-! The literal parity product as finite Laurent coefficients. Its entire
evaluation and original quarter phase are proved, rather than certified. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The actual rank-two integer frequency map. -/
def rankTwoFrequencyHom : (ℤ × ℤ) →+ ℝ where
  toFun n := n.1 + beta * n.2
  map_zero' := by simp
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

theorem rankTwoFrequencyHom_apply (n : ℤ × ℤ) :
    rankTwoFrequencyHom n = (n.1 : ℝ) + beta * n.2 := rfl

theorem rankTwoFrequencyHom_injective : Function.Injective rankTwoFrequencyHom := by
  intro p q h
  have hn : p.2 = q.2 := by
    by_contra hn
    have hd : p.2 - q.2 ≠ 0 := sub_ne_zero.mpr hn
    apply beta_irrational.ne_rational (q.1 - p.1) (p.2 - q.2)
    apply (eq_div_iff (by exact_mod_cast hd : ((p.2 - q.2 : ℤ) : ℝ) ≠ 0)).mpr
    simp only [Int.cast_sub]
    change (p.1 : ℝ) + beta * p.2 = q.1 + beta * q.2 at h
    linarith
  apply Prod.ext
  · change (p.1 : ℝ) + beta * p.2 = q.1 + beta * q.2 at h
    rw [hn] at h
    exact_mod_cast (show (p.1 : ℝ) = q.1 by linarith)
  · exact hn

/-- Entire characters for the actual additive integer lattice. -/
def rankTwoEntireCharacter (z : ℂ) : Multiplicative (ℤ × ℤ) →* ℂ where
  toFun n := complexUnitPhase ((rankTwoFrequencyHom n.toAdd : ℝ) * z)
  map_one' := by simp [complexUnitPhase]
  map_mul' a b := by
    change complexUnitPhase ((rankTwoFrequencyHom (a.toAdd + b.toAdd) : ℝ) * z) = _
    simp only [map_add, Complex.ofReal_add,
      add_mul, complexUnitPhase, mul_add, Complex.exp_add]

theorem rankTwoEntireCharacter_apply (z : ℂ) (n : ℤ × ℤ) :
    rankTwoEntireCharacter z (Multiplicative.ofAdd n) =
      complexUnitPhase ((rankTwoFrequencyHom n : ℝ) * z) := rfl

/-- The actual entire evaluation of finite Laurent polynomials. -/
def rankTwoLaurentEvaluation (z : ℂ) : AddMonoidAlgebra ℂ (ℤ × ℤ) →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (ℤ × ℤ) (rankTwoEntireCharacter z)

theorem rankTwoEntireCharacter_ofReal (n : ℤ × ℤ) (x : ℝ) :
    rankTwoEntireCharacter x (Multiplicative.ofAdd n) =
      combModulationCharacter (rankTwoFrequencyHom n) x := by
  rw [combModulationCharacter_eq_exp]
  rw [rankTwoEntireCharacter_apply]
  unfold complexUnitPhase
  congr 1
  push_cast
  ring

theorem rankTwoLaurentEvaluation_ofReal (p : AddMonoidAlgebra ℂ (ℤ × ℤ)) (x : ℝ) :
    rankTwoLaurentEvaluation x p = annihilatorExponentialSymbol rankTwoFrequencyHom p.coeff x := by
  rw [rankTwoLaurentEvaluation, AddMonoidAlgebra.lift_apply']
  simp only [Finsupp.sum, Algebra.algebraMap_self, RingHom.id_apply,
    rankTwoEntireCharacter_ofReal, annihilatorExponentialSymbol]

/-- The original sheet, including the quarter phase in both W coefficients. -/
def sheetLaurentPolynomial (a : ℝ) : AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  AddMonoidAlgebra.single (0, 0) 1 -
    AddMonoidAlgebra.single (0, 1) ((a : ℂ) * complexUnitPhase (-1 / 4)) +
    AddMonoidAlgebra.single (1, 0) (a : ℂ) -
    AddMonoidAlgebra.single (1, 1) (complexUnitPhase (-1 / 4))

theorem rankTwoLaurentEvaluation_sheet (a : ℝ) (z : ℂ) :
    rankTwoLaurentEvaluation z (sheetLaurentPolynomial a) = complexSheetFlow a z := by
  have hw : complexUnitPhase (-1 / 4) * complexUnitPhase (beta * z) =
      complexUnitPhase (beta * z - 1 / 4) := by
    unfold complexUnitPhase
    rw [← Complex.exp_add]
    congr 1
    ring
  have hzw : complexUnitPhase ((1 + (beta : ℝ) : ℝ) * z) =
      complexUnitPhase z * complexUnitPhase (beta * z) := by
    unfold complexUnitPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [sheetLaurentPolynomial, map_sub, map_add, rankTwoLaurentEvaluation,
    AddMonoidAlgebra.lift_single, smul_eq_mul]
  simp only [rankTwoEntireCharacter_apply, rankTwoFrequencyHom_apply, Int.cast_zero, Int.cast_one,
    mul_zero, add_zero, zero_add, mul_one, Complex.ofReal_zero, zero_mul,
    Complex.ofReal_one, one_mul]
  rw [hzw]
  rw [show complexUnitPhase 0 = 1 by simp [complexUnitPhase]]
  unfold complexSheetFlow sheetPolynomial
  rw [← hw]
  ring

/-- The complete original finite product as an actual Laurent polynomial. -/
def productLaurentPolynomial (s : ℕ) : AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  ∏ i : Fin s, sheetLaurentPolynomial (productSheetParameter s i)

/-- The finite coefficients of the literal original product. -/
def productLaurentCoefficients (s : ℕ) : (ℤ × ℤ) →₀ ℂ :=
  (productLaurentPolynomial s).coeff

theorem rankTwoLaurentEvaluation_product (s : ℕ) (z : ℂ) :
    rankTwoLaurentEvaluation z (productLaurentPolynomial s) = complexSheetProduct s z := by
  simp only [productLaurentPolynomial, map_prod, rankTwoLaurentEvaluation_sheet, complexSheetProduct]

/-- Nontriviality is discharged by the actual entire product away from R. -/
theorem productLaurentCoefficients_ne_zero (s : ℕ) : productLaurentCoefficients s ≠ 0 := by
  intro h
  have hp : productLaurentPolynomial s = 0 := by
    apply AddMonoidAlgebra.coeff_injective
    exact h
  have he := rankTwoLaurentEvaluation_product s Complex.I
  rw [hp, map_zero] at he
  have hreal := complexSheetProduct_root_real s he.symm
  norm_num at hreal

/-- The actual finite symbol vanishes on EVERY original complete product root. -/
theorem productLaurentSymbol_vanishes (s : ℕ) (x : ℝ)
    (hx : x ∈ (productSheetCarrier s).carrier) :
    annihilatorExponentialSymbol rankTwoFrequencyHom (productLaurentCoefficients s) x = 0 := by
  change annihilatorExponentialSymbol rankTwoFrequencyHom (productLaurentPolynomial s).coeff x = 0
  rw [← rankTwoLaurentEvaluation_ofReal (productLaurentPolynomial s) x, rankTwoLaurentEvaluation_product,
    complexSheetProduct_ofReal]
  exact hx

end

end MeyerGeneralProblem.StrongParity
