module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductAnnihilator

@[expose] public section

/-! Complete original ProductAnnihilator for actual compact parameter blocks.
Every original supported pair is retained, without a constructed-image premise. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The complete original finite product as an actual Laurent polynomial. -/
def productLaurentPolynomial {s : ℕ} (block : CompactOriginalParameterBlock s) : AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  ∏ i : Fin s, sheetLaurentPolynomial (block.parameter i)

/-- The finite coefficients of the literal original product. -/
def productLaurentCoefficients {s : ℕ} (block : CompactOriginalParameterBlock s) : (ℤ × ℤ) →₀ ℂ :=
  (productLaurentPolynomial block).coeff

theorem rankTwoLaurentEvaluation_product {s : ℕ} (block : CompactOriginalParameterBlock s) (z : ℂ) :
    rankTwoLaurentEvaluation z (productLaurentPolynomial block) = compactOriginalComplexSheetProduct block z := by
  simp only [productLaurentPolynomial, map_prod, rankTwoLaurentEvaluation_sheet, compactOriginalComplexSheetProduct]

/-- Nontriviality is discharged by the actual entire product away from R. -/
theorem productLaurentCoefficients_ne_zero {s : ℕ} (block : CompactOriginalParameterBlock s) : productLaurentCoefficients block ≠ 0 := by
  intro h
  have hp : productLaurentPolynomial block = 0 := by
    apply AddMonoidAlgebra.coeff_injective
    exact h
  have he := rankTwoLaurentEvaluation_product block Complex.I
  rw [hp, map_zero] at he
  have hreal := compactOriginalComplexSheetProduct_root_real block he.symm
  norm_num at hreal

/-- The actual finite symbol vanishes on EVERY original complete product root. -/
theorem productLaurentSymbol_vanishes {s : ℕ} (block : CompactOriginalParameterBlock s) (x : ℝ)
    (hx : x ∈ (compactOriginalProductSheetCarrier block).carrier) :
    annihilatorExponentialSymbol rankTwoFrequencyHom (productLaurentCoefficients block) x = 0 := by
  change annihilatorExponentialSymbol rankTwoFrequencyHom (productLaurentPolynomial block).coeff x = 0
  rw [← rankTwoLaurentEvaluation_ofReal (productLaurentPolynomial block) x, rankTwoLaurentEvaluation_product,
    compactOriginalComplexSheetProduct_ofReal]
  exact hx

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
