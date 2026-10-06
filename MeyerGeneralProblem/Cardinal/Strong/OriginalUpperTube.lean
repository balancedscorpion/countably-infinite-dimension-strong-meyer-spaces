module

public import MeyerGeneralProblem.Cardinal.Strong.ProductPairFiniteDimension
public import MeyerGeneralProblem.Cardinal.Strong.ProductFourierPair
public import MeyerGeneralProblem.Cardinal.Strong.LaurentConvolutionSeries

@[expose] public section

/-! The actual original positive Fourier array of the slab construction,
including zero extension to the complete integer lattice and absolute sums. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped FourierTransform

/-- The literal nonnegative cone label embedded in the integer frequency lattice. -/
def natPairIntegerIndex (p : ℕ × ℕ) : ℤ × ℤ := ((p.1 : ℤ), (p.2 : ℤ))

theorem natPairIntegerIndex_injective : Function.Injective natPairIntegerIndex := by
  intro p q h
  change ((p.1 : ℤ), (p.2 : ℤ)) = ((q.1 : ℤ), (q.2 : ℤ)) at h
  apply Prod.ext
  · have h₁ : (p.1 : ℤ) = q.1 := congrArg Prod.fst h
    exact_mod_cast h₁
  · have h₂ : (p.2 : ℤ) = q.2 := congrArg Prod.snd h
    exact_mod_cast h₂

theorem natPairIntegerIndex_range (n : ℤ × ℤ) :
    n ∈ Set.range natPairIntegerIndex ↔ 0 ≤ n.1 ∧ 0 ≤ n.2 := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  · intro hn
    exact ⟨(n.1.toNat, n.2.toNat), Prod.ext (Int.toNat_of_nonneg hn.1) (Int.toNat_of_nonneg hn.2)⟩

theorem rankTwoFrequencyHom_natPair (p : ℕ × ℕ) :
    rankTwoFrequencyHom (natPairIntegerIndex p) = positiveConeFrequency p := by
  simp [rankTwoFrequencyHom_apply, natPairIntegerIndex, positiveConeFrequency]

theorem productPhysical_originalFourierArray_positive (s : ℕ)
    (r : productNumeratorIndex s → ℂ) (p : ℕ × ℕ) :
    originalFourierArray rankTwoFrequencyHom spectralConeCarrier
      (productPhysicalDistribution s r) (natPairIntegerIndex p) =
        productConeIndexCoefficient s r (.inl p) := by
  classical
  unfold originalFourierArray
  rw [rankTwoFrequencyHom_natPair, productPhysical_fourier_eq_spectral]
  have hx : positiveConeFrequency p ∈ spectralConeCarrier.carrier :=
    (spectralConeIndexPoint (.inl p)).property
  unfold extendedAtomicCoefficient
  rw [dite_eq_left hx]
  exact (productSpectralDistribution_isolation s r (spectralConeIndexPoint (.inl p))).trans
    (productSpectralCoefficient_at_label s r (.inl p))

theorem productPhysical_originalPositiveCut_at_natPair (s : ℕ)
    (r : productNumeratorIndex s → ℂ) (p : ℕ × ℕ) :
    arrayPositiveCut rankTwoFrequencyHom 0
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
        (productPhysicalDistribution s r)) (natPairIntegerIndex p) =
      productConeIndexCoefficient s r (.inl p) := by
  classical
  unfold arrayPositiveCut
  rw [ite_eq_left (by rw [rankTwoFrequencyHom_natPair]; exact positiveConeFrequency_nonneg p)]
  exact productPhysical_originalFourierArray_positive s r p

/-- The actual original integer array has the retained quotient as its upper
half-plane sum. Every lattice point outside the positive cone has coefficient zero. -/
theorem productPhysical_originalPositiveCut_hasSum (s : ℕ)
    (r : productNumeratorIndex s → ℂ) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun n : ℤ × ℤ =>
      arrayPositiveCut rankTwoFrequencyHom 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
          (productPhysicalDistribution s r)) n *
        rankTwoEntireCharacter z (Multiplicative.ofAdd n))
      (complexProductSlabQuotient s r z) := by
  have hzero (n : ℤ × ℤ) (hn : n ∉ Set.range natPairIntegerIndex) :
      arrayPositiveCut rankTwoFrequencyHom 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
          (productPhysicalDistribution s r)) n *
        rankTwoEntireCharacter z (Multiplicative.ofAdd n) = 0 := by
    have hc : arrayPositiveCut rankTwoFrequencyHom 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier
          (productPhysicalDistribution s r)) n = 0 := by
      by_contra hc
      exact hn ((natPairIntegerIndex_range n).mpr
        (originalPositiveCut_coordinate_nonneg _ hc))
    rw [hc, zero_mul]
  apply (natPairIntegerIndex_injective.hasSum_iff hzero).mp
  convert! productUpperTube_hasSum s r hz using 1
  · funext p
    simp only [Function.comp_def, productPhysical_originalPositiveCut_at_natPair,
      rankTwoEntireCharacter_apply, rankTwoFrequencyHom_natPair]

end

end MeyerGeneralProblem.StrongParity
