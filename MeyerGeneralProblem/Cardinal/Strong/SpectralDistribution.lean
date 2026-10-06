module

public import MeyerGeneralProblem.Cardinal.Strong.SpectralConeIndex
public import MeyerGeneralProblem.Cardinal.Strong.SlabZeroCoefficient
public import MeyerGeneralProblem.Distribution.WeightedAtomic

@[expose] public section

/-! The genuine weighted atomic spectral record of every complete original slab.
The Fourier identity with the physical record is a separate obligation. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The literal upper-minus-lower spectral sum on the COMPLETE original coarse cone. -/
def productSpectralDistribution (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    TemperedDistribution ℝ ℂ :=
  weightedAtomicDistribution spectralConeCarrier (productSpectralCoefficient s r)
    (s + 3) (productSpectralCoefficient_weight_summable s r)

theorem productSpectralDistribution_apply (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (f : SchwartzMap ℝ ℂ) :
    productSpectralDistribution s r f =
      ∑' x : spectralConeCarrier.subtype, productSpectralCoefficient s r x * f x := rfl

theorem productSpectralDistribution_atomicOnCarrier (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    AtomicOnCarrier spectralConeCarrier (productSpectralDistribution s r) :=
  weightedAtomicDistribution_atomicOnCarrier _ _ _ _

theorem productSpectralDistribution_isLocallyAtomicCoefficientFamily
    (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    IsLocallyAtomicCoefficientFamily spectralConeCarrier
      (productSpectralDistribution s r) (productSpectralCoefficient s r) :=
  weightedAtomicDistribution_isLocallyAtomicCoefficientFamily _ _ _ _

theorem productSpectralDistribution_isolation (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : spectralConeCarrier.subtype) :
    productSpectralDistribution s r (spectralConeCarrier.isolationSchwartz x) =
      productSpectralCoefficient s r x := weightedAtomicDistribution_isolation _ _ _ _ _

/-- Actual spectral strong admission, with all coefficient estimates discharged. -/
theorem productSpectralDistribution_mem_strongExponent (s : ℕ)
    (r : productNumeratorIndex s → ℂ) :
    productSpectralDistribution s r ∈ stronglyTemperedAtomicAtExponent spectralConeCarrier (s + 3) :=
  weightedAtomicDistribution_mem_strongExponent _ _ _ _

theorem productSpectralDistribution_mem_strongAtomic (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    productSpectralDistribution s r ∈ StronglyTemperedAtomicOnCarrier spectralConeCarrier := by
  apply (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
  exact ⟨s + 3, productSpectralDistribution_mem_strongExponent s r⟩

/-- The exact zero-frequency mass includes the original complete upper constant term. -/
theorem productSpectralDistribution_zero_isolation (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    productSpectralDistribution s r
      (spectralConeCarrier.isolationSchwartz (spectralConeIndexPoint (.inl (0, 0)))) =
        productSlabPolynomial s r 0 0 := by
  calc
    _ = productConeIndexCoefficient s r (.inl (0, 0)) :=
      (productSpectralDistribution_isolation s r _).trans
        (productSpectralCoefficient_at_label s r _)
    _ = _ := by
      simp only [productConeIndexCoefficient, Nat.cast_zero, neg_zero, zero_div]
      have hz : unitPhase 0 = 1 := by simp [unitPhase]
      rw [hz, mul_one, productSlabUpperCoefficient_zero_zero]

end

end MeyerGeneralProblem.StrongParity
