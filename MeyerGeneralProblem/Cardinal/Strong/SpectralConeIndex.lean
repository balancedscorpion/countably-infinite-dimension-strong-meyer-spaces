module

public import MeyerGeneralProblem.Cardinal.Strong.ConeWeights

@[expose] public section

/-! A literal bijection onto the full coarse cone with zero counted once,
and original quarter-phase upper-minus-lower coefficients. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- All positive labels and all nonzero negative labels. No cone point is omitted. -/
def spectralConeIndex := (ℕ × ℕ) ⊕ {p : ℕ × ℕ // p ≠ (0, 0)}

/-- The signed real frequency of every complete cone label. -/
def spectralConeIndexFrequency : spectralConeIndex → ℝ
  | .inl p => positiveConeFrequency p
  | .inr p => -positiveConeFrequency p

theorem spectralConeIndexFrequency_injective : Function.Injective spectralConeIndexFrequency := by
  rintro (p | p) (q | q) h
  · exact congrArg Sum.inl (positiveConeFrequency_injective h)
  · have hq : positiveConeFrequency q = 0 := by
      have hp0 := positiveConeFrequency_nonneg p
      have hq0 := positiveConeFrequency_nonneg q
      change positiveConeFrequency p = -positiveConeFrequency q at h
      linarith
    exact False.elim (q.property ((positiveConeFrequency_eq_zero_iff q).mp hq))
  · have hp : positiveConeFrequency p = 0 := by
      have hp0 := positiveConeFrequency_nonneg p
      have hq0 := positiveConeFrequency_nonneg q
      change -positiveConeFrequency p = positiveConeFrequency q at h
      linarith
    exact False.elim (p.property ((positiveConeFrequency_eq_zero_iff p).mp hp))
  · apply congrArg Sum.inr
    apply Subtype.ext
    exact positiveConeFrequency_injective (neg_injective h)

/-- Each label as its actual point of the complete locally finite carrier. -/
def spectralConeIndexPoint (p : spectralConeIndex) : spectralConeCarrier.subtype :=
  ⟨spectralConeIndexFrequency p, by
    rcases p with p | p
    · exact ⟨(false, p), rfl⟩
    · exact ⟨(true, p), rfl⟩⟩

theorem spectralConeIndexPoint_bijective : Function.Bijective spectralConeIndexPoint := by
  constructor
  · intro p q h
    apply spectralConeIndexFrequency_injective
    exact congrArg Subtype.val h
  · intro x
    obtain ⟨⟨b, p⟩, hx⟩ := x.property
    cases b
    · exact ⟨.inl p, Subtype.ext (by simpa only [signedConeFrequency, Bool.false_eq_true,
        ite_false, spectralConeIndexPoint, spectralConeIndexFrequency] using hx)⟩
    · by_cases hp : p = (0, 0)
      · exact ⟨.inl (0, 0), Subtype.ext (by
          simpa only [signedConeFrequency, ite_true, hp, positiveConeFrequency,
            Nat.cast_zero, mul_zero, add_zero, neg_zero, spectralConeIndexPoint,
            spectralConeIndexFrequency] using hx)⟩
      · exact ⟨.inr ⟨p, hp⟩, Subtype.ext (by
          simpa only [signedConeFrequency, ite_true, spectralConeIndexPoint,
            spectralConeIndexFrequency] using hx)⟩

/-- The genuine complete carrier parametrization, including zero exactly once. -/
def spectralConeEquiv : spectralConeIndex ≃ spectralConeCarrier.subtype :=
  Equiv.ofBijective spectralConeIndexPoint spectralConeIndexPoint_bijective

/-- Literal jump coefficients with the original quarter phases and both signs. -/
def productConeIndexCoefficient (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    spectralConeIndex → ℂ
  | .inl p => productSlabUpperCoefficient s r p.1 p.2 * unitPhase (-(p.2 : ℝ) / 4)
  | .inr p => -productSlabLowerCoefficient s r p.val.1 p.val.2 * unitPhase ((p.val.2 : ℝ) / 4)

theorem productConeIndexCoefficient_weight_summable (s : ℕ)
    (r : productNumeratorIndex s → ℂ) :
    Summable (fun p : spectralConeIndex => ‖productConeIndexCoefficient s r p‖ /
      (1 + |spectralConeIndexFrequency p|) ^ (s + 3)) := by
  apply Summable.sum
  · change Summable (fun p : ℕ × ℕ => ‖productConeIndexCoefficient s r (.inl p)‖ /
      (1 + |spectralConeIndexFrequency (.inl p)|) ^ (s + 3))
    simpa only [productConeIndexCoefficient, spectralConeIndexFrequency,
      norm_mul, unitPhase_norm, mul_one, abs_of_nonneg (positiveConeFrequency_nonneg _)] using
        productSlabUpperCoefficient_weight_summable s r
  · change Summable (fun p : {p : ℕ × ℕ // p ≠ (0, 0)} =>
      ‖productConeIndexCoefficient s r (.inr p)‖ /
      (1 + |spectralConeIndexFrequency (.inr p)|) ^ (s + 3))
    have hn := (productSlabLowerCoefficient_weight_summable s r).comp_injective
      (Subtype.val_injective (p := fun p : ℕ × ℕ => p ≠ (0, 0)))
    convert! hn using 1
    funext p
    simp only [Function.comp_def, productConeIndexCoefficient, spectralConeIndexFrequency,
      norm_mul, norm_neg, unitPhase_norm, mul_one, abs_neg,
      abs_of_nonneg (positiveConeFrequency_nonneg _)]

/-- Original jump coefficients on the actual complete coarse carrier. -/
def productSpectralCoefficient (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : spectralConeCarrier.subtype) : ℂ :=
  productConeIndexCoefficient s r (spectralConeEquiv.symm x)

theorem productSpectralCoefficient_at_label (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (p : spectralConeIndex) :
    productSpectralCoefficient s r (spectralConeIndexPoint p) = productConeIndexCoefficient s r p := by
  change productConeIndexCoefficient s r (spectralConeEquiv.symm (spectralConeEquiv p)) = _
  rw [Equiv.symm_apply_apply]

theorem productSpectralCoefficient_weight_summable (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    Summable (fun x : spectralConeCarrier.subtype =>
      ‖productSpectralCoefficient s r x‖ / (1 + |(x : ℝ)|) ^ (s + 3)) := by
  apply spectralConeEquiv.summable_iff.mp
  change Summable (fun p : spectralConeIndex =>
    ‖productSpectralCoefficient s r (spectralConeIndexPoint p)‖ /
      (1 + |spectralConeIndexFrequency p|) ^ (s + 3))
  simpa only [productSpectralCoefficient_at_label] using
    productConeIndexCoefficient_weight_summable s r

end

end MeyerGeneralProblem.StrongParity
