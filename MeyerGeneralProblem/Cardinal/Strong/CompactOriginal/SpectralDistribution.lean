module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.SpectralDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralConeIndex
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SlabZeroCoefficient

@[expose] public section

/-! Original SpectralDistribution for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The literal upper-minus-lower spectral sum on the COMPLETE original coarse cone. -/
def productSpectralDistribution {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    TemperedDistribution ℝ ℂ :=
  weightedAtomicDistribution spectralConeCarrier (productSpectralCoefficient block r)
    (s + 3) (productSpectralCoefficient_weight_summable block r)

theorem productSpectralDistribution_apply {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (f : SchwartzMap ℝ ℂ) :
    productSpectralDistribution block r f =
      ∑' x : spectralConeCarrier.subtype, productSpectralCoefficient block r x * f x := rfl

theorem productSpectralDistribution_atomicOnCarrier {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    AtomicOnCarrier spectralConeCarrier (productSpectralDistribution block r) :=
  weightedAtomicDistribution_atomicOnCarrier _ _ _ _

theorem productSpectralDistribution_isLocallyAtomicCoefficientFamily
    {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    IsLocallyAtomicCoefficientFamily spectralConeCarrier
      (productSpectralDistribution block r) (productSpectralCoefficient block r) :=
  weightedAtomicDistribution_isLocallyAtomicCoefficientFamily _ _ _ _

theorem productSpectralDistribution_isolation {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : spectralConeCarrier.subtype) :
    productSpectralDistribution block r (spectralConeCarrier.isolationSchwartz x) =
      productSpectralCoefficient block r x := weightedAtomicDistribution_isolation _ _ _ _ _

/-- Actual spectral strong admission, with all coefficient estimates discharged. -/
theorem productSpectralDistribution_mem_strongExponent {s : ℕ} (block : CompactOriginalParameterBlock s)
    (r : productNumeratorIndex s → ℂ) :
    productSpectralDistribution block r ∈ stronglyTemperedAtomicAtExponent spectralConeCarrier (s + 3) :=
  weightedAtomicDistribution_mem_strongExponent _ _ _ _

theorem productSpectralDistribution_mem_strongAtomic {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    productSpectralDistribution block r ∈ StronglyTemperedAtomicOnCarrier spectralConeCarrier := by
  apply (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
  exact ⟨s + 3, productSpectralDistribution_mem_strongExponent block r⟩

/-- The exact zero-frequency mass includes the original complete upper constant term. -/
theorem productSpectralDistribution_zero_isolation {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    productSpectralDistribution block r
      (spectralConeCarrier.isolationSchwartz (spectralConeIndexPoint (.inl (0, 0)))) =
        productSlabPolynomial s r 0 0 := by
  calc
    _ = productConeIndexCoefficient block r (.inl (0, 0)) :=
      (productSpectralDistribution_isolation block r _).trans
        (productSpectralCoefficient_at_label block r _)
    _ = _ := by
      simp only [productConeIndexCoefficient, Nat.cast_zero, neg_zero, zero_div]
      have hz : unitPhase 0 = 1 := by simp [unitPhase]
      rw [hz, mul_one, productSlabUpperCoefficient_zero_zero]

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
