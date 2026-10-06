module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalUpperTube
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.PhysicalDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductAnnihilator
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductFourierPair
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPoleMass
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductReverseNumerator
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductInverseNumerator

@[expose] public section

/-! Complete original ProductInverseNumerator for actual compact parameter blocks.
Every original supported pair is retained, without a constructed-image premise. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open scoped FourierTransform

theorem complexSheetProduct_ne_zero_upper {s : ℕ} (block : CompactOriginalParameterBlock s) {z : ℂ} (hz : 0 < z.im) :
    compactOriginalComplexSheetProduct block z ≠ 0 := by
  intro h
  have hreal := compactOriginalComplexSheetProduct_root_real block h
  linarith

/-- Equality on the WHOLE integer lattice of the actual original numerator
and the literal quarter-phased slab polynomial. -/
theorem productPhysical_cutNumerator_eq_slab {s : ℕ} (block : CompactOriginalParameterBlock s)
    (r : productNumeratorIndex s → ℂ) :
    cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients block) 0
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
        (productPhysicalDistribution block r)) = (productSlabLaurentPolynomial s r).coeff := by
  obtain ⟨R, hR⟩ := product_originalFourierPair_exists_finite_numerator block
    (productPhysicalDistribution block r) (productPhysicalDistribution_atomicOnCarrier block r)
    (by rw [productPhysical_fourier_eq_spectral]; exact productSpectralDistribution_atomicOnCarrier block r) 0
  have heq : AddMonoidAlgebra.ofCoeff R = productSlabLaurentPolynomial s r := by
    apply rankTwoLaurentEvaluation_injective
    intro z hz
    have hconv := rankTwoLaurentConvolution_hasSum (productLaurentPolynomial block)
      (arrayPositiveCut rankTwoFrequencyHom 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
          (productPhysicalDistribution block r))) z (complexProductSlabQuotient block r z)
      (productPhysical_originalPositiveCut_hasSum block r hz)
    have hfinite := rankTwoLaurentEvaluation_hasSum (AddMonoidAlgebra.ofCoeff R) z
    have hconv' : HasSum (fun n => R n * rankTwoEntireCharacter z (Multiplicative.ofAdd n))
        (rankTwoLaurentEvaluation z (productLaurentPolynomial block) * complexProductSlabQuotient block r z) := by
      apply hconv.congr_fun
      intro n
      rw [(hR n).1]
      rfl
    calc
      rankTwoLaurentEvaluation z (AddMonoidAlgebra.ofCoeff R) =
          rankTwoLaurentEvaluation z (productLaurentPolynomial block) *
            complexProductSlabQuotient block r z := hfinite.unique hconv'
      _ = complexProductSlabNumerator s r z := by
        rw [rankTwoLaurentEvaluation_product, complexProductSlabQuotient]
        field_simp [complexSheetProduct_ne_zero_upper block hz]
      _ = rankTwoLaurentEvaluation z (productSlabLaurentPolynomial s r) :=
        (rankTwoLaurentEvaluation_slab s r z).symm
  funext n
  exact (hR n).1.symm.trans (congrArg (fun p : AddMonoidAlgebra ℂ (ℤ × ℤ) => p.coeff n) heq)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
