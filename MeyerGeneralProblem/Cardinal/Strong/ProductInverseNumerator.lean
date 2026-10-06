module

public import MeyerGeneralProblem.Cardinal.Strong.SlabLaurentPolynomial

@[expose] public section

/-! The actual original cut numerator of EVERY original slab construction.
The convergent original tube series is multiplied by the finite annihilator;
faithful entire Laurent evaluation then recovers every integer coefficient. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped FourierTransform

theorem complexSheetProduct_ne_zero_upper (s : ℕ) {z : ℂ} (hz : 0 < z.im) :
    complexSheetProduct s z ≠ 0 := by
  intro h
  have hreal := complexSheetProduct_root_real s h
  linarith

/-- Equality on the WHOLE integer lattice of the actual original numerator
and the literal quarter-phased slab polynomial. -/
theorem productPhysical_cutNumerator_eq_slab (s : ℕ)
    (r : productNumeratorIndex s → ℂ) :
    cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients s) 0
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
        (productPhysicalDistribution s r)) = (productSlabLaurentPolynomial s r).coeff := by
  obtain ⟨R, hR⟩ := product_originalFourierPair_exists_finite_numerator s
    (productPhysicalDistribution s r) (productPhysicalDistribution_atomicOnCarrier s r)
    (by rw [productPhysical_fourier_eq_spectral]; exact productSpectralDistribution_atomicOnCarrier s r) 0
  have heq : AddMonoidAlgebra.ofCoeff R = productSlabLaurentPolynomial s r := by
    apply rankTwoLaurentEvaluation_injective
    intro z hz
    have hconv := rankTwoLaurentConvolution_hasSum (productLaurentPolynomial s)
      (arrayPositiveCut rankTwoFrequencyHom 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
          (productPhysicalDistribution s r))) z (complexProductSlabQuotient s r z)
      (productPhysical_originalPositiveCut_hasSum s r hz)
    have hfinite := rankTwoLaurentEvaluation_hasSum (AddMonoidAlgebra.ofCoeff R) z
    have hconv' : HasSum (fun n => R n * rankTwoEntireCharacter z (Multiplicative.ofAdd n))
        (rankTwoLaurentEvaluation z (productLaurentPolynomial s) * complexProductSlabQuotient s r z) := by
      apply hconv.congr_fun
      intro n
      rw [(hR n).1]
      rfl
    calc
      rankTwoLaurentEvaluation z (AddMonoidAlgebra.ofCoeff R) =
          rankTwoLaurentEvaluation z (productLaurentPolynomial s) *
            complexProductSlabQuotient s r z := hfinite.unique hconv'
      _ = complexProductSlabNumerator s r z := by
        rw [rankTwoLaurentEvaluation_product, complexProductSlabQuotient]
        field_simp [complexSheetProduct_ne_zero_upper s hz]
      _ = rankTwoLaurentEvaluation z (productSlabLaurentPolynomial s r) :=
        (rankTwoLaurentEvaluation_slab s r z).symm
  funext n
  exact (hR n).1.symm.trans (congrArg (fun p : AddMonoidAlgebra ℂ (ℤ × ℤ) => p.coeff n) heq)

end

end MeyerGeneralProblem.StrongParity
