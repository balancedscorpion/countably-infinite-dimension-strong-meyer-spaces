module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ReciprocalSlabSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SlabCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.SpectralConeIndex
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ConeWeights

@[expose] public section

/-! Original SpectralConeIndex for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- Literal jump coefficients with the original quarter phases and both signs. -/
def productConeIndexCoefficient {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    spectralConeIndex → ℂ
  | .inl p => productSlabUpperCoefficient block r p.1 p.2 * unitPhase (-(p.2 : ℝ) / 4)
  | .inr p => -productSlabLowerCoefficient block r p.val.1 p.val.2 * unitPhase ((p.val.2 : ℝ) / 4)

theorem productConeIndexCoefficient_weight_summable {s : ℕ} (block : CompactOriginalParameterBlock s)
    (r : productNumeratorIndex s → ℂ) :
    Summable (fun p : spectralConeIndex => ‖productConeIndexCoefficient block r p‖ /
      (1 + |spectralConeIndexFrequency p|) ^ (s + 3)) := by
  apply Summable.sum
  · change Summable (fun p : ℕ × ℕ => ‖productConeIndexCoefficient block r (.inl p)‖ /
      (1 + |spectralConeIndexFrequency (.inl p)|) ^ (s + 3))
    simpa only [productConeIndexCoefficient, spectralConeIndexFrequency,
      norm_mul, unitPhase_norm, mul_one, abs_of_nonneg (positiveConeFrequency_nonneg _)] using
        productSlabUpperCoefficient_weight_summable block r
  · change Summable (fun p : {p : ℕ × ℕ // p ≠ (0, 0)} =>
      ‖productConeIndexCoefficient block r (.inr p)‖ /
      (1 + |spectralConeIndexFrequency (.inr p)|) ^ (s + 3))
    have hn := (productSlabLowerCoefficient_weight_summable block r).comp_injective
      (Subtype.val_injective (p := fun p : ℕ × ℕ => p ≠ (0, 0)))
    convert! hn using 1
    funext p
    simp only [Function.comp_def, productConeIndexCoefficient, spectralConeIndexFrequency,
      norm_mul, norm_neg, unitPhase_norm, mul_one, abs_neg,
      abs_of_nonneg (positiveConeFrequency_nonneg _)]

/-- Original jump coefficients on the actual complete coarse carrier. -/
def productSpectralCoefficient {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : spectralConeCarrier.subtype) : ℂ :=
  productConeIndexCoefficient block r (spectralConeEquiv.symm x)

theorem productSpectralCoefficient_at_label {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (p : spectralConeIndex) :
    productSpectralCoefficient block r (spectralConeIndexPoint p) = productConeIndexCoefficient block r p := by
  change productConeIndexCoefficient block r (spectralConeEquiv.symm (spectralConeEquiv p)) = _
  rw [Equiv.symm_apply_apply]

theorem productSpectralCoefficient_weight_summable {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    Summable (fun x : spectralConeCarrier.subtype =>
      ‖productSpectralCoefficient block r x‖ / (1 + |(x : ℝ)|) ^ (s + 3)) := by
  apply spectralConeEquiv.summable_iff.mp
  change Summable (fun p : spectralConeIndex =>
    ‖productSpectralCoefficient block r (spectralConeIndexPoint p)‖ /
      (1 + |spectralConeIndexFrequency p|) ^ (s + 3))
  simpa only [productSpectralCoefficient_at_label] using
    productConeIndexCoefficient_weight_summable block r

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
