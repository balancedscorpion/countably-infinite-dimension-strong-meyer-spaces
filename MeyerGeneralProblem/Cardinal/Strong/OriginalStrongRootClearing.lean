module

public import MeyerGeneralProblem.Cardinal.Strong.PositiveConeClearingGeometry

@[expose] public section

/-!
# Actual zero-output clearing of BOTH ORIGINAL strong records

For an ordinary finite positive native polynomial vanishing on the actual
root part, construct the genuine f*T, its actual Fourier convolution, and
ALL translated clearing factors internally. Whole carrier geometry and
same-exponent original TV bounds supply both final records. Strong no-return
proves the TRUE cleared distribution zero; no cleared-output certificate or
Fourier admissibility of a raw restriction is an input.
-/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The actual g_+*F(f*T), with every input frequency included in g_+ internally. -/
def originalStrongRootClearedFourierDistribution {ι : Type*} [Fintype ι]
    (scale : ℝ) (p : ι → ℕ × ℕ) (c : ι → ℂ) (T : TemperedDistribution ℝ ℂ) :
    TemperedDistribution ℝ ℂ :=
  let a := originalPositivePolynomialFrequency scale p
  finiteTranslatedSymbolProduct a c (finiteRootClearingShifts a)
    (𝓕 (finiteExponentialMultiplication a c T))

/-- GENUINE zero-output clearing for EVERY original strong Fourier pair.
Only ordinary native polynomial/root geometry and the two original input records
are premises. All finite product factors, transported weights, whole final support
bounds, Fourier square and the no-return conclusion are supplied internally. -/
theorem originalStrongRootClearedFourierDistribution_eq_zero {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (A : Set ℝ) (m : ℕ) (hm : 0 < m)
    (p : ι → ℕ × ℕ) (c : ι → ℂ)
    (hS : S.carrier ⊆ A ∪ (scaledTranslatedConeCarrier 0 0 (originalPrivateScale m)
      (originalPrivateScale_pos m hm)).carrier)
    (hroot : ∀ x ∈ A, finitePositiveExponentialSymbol
      (originalPositivePolynomialFrequency (originalPrivateScale m) p) c x = 0)
    (M N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) :
    originalStrongRootClearedFourierDistribution (originalPrivateScale m) p c T = 0 := by
  let scale := originalPrivateScale m
  have hs : 0 < scale := originalPrivateScale_pos m hm
  let K := scaledTranslatedConeCarrier 0 0 scale hs
  let a := originalPositivePolynomialFrequency scale p
  let r := finiteRootClearingShifts a
  let U := finiteExponentialMultiplication a c T
  let D := 𝓕 U
  let G := finiteTranslatedSymbolProduct a c r D
  let P : ℤ := (originalPositivePolynomialBudget p).1
  let Q : ℤ := (originalPositivePolynomialBudget p).2
  have hUS : U ∈ stronglyTemperedAtomicAtExponent S M :=
    stronglyTemperedAtomicAtExponent_finiteExponentialMultiplication S M T hT a c
  have hUK : U ∈ stronglyTemperedAtomicAtExponent K M := by
    apply stronglyTemperedAtomicAtExponent_of_originalRows_zero S K M U hUS
    intro x hx
    rw [finiteExponentialMultiplication_isolation_apply S T hT.1]
    have hxA : (x : ℝ) ∈ A := (hS x.property).resolve_right hx
    rw [hroot x hxA, zero_mul]
  have hDS : D ∈ stronglyTemperedAtomicAtExponent (finiteCombConvolutionCarrier S a) N :=
    (stronglyTemperedOriginalPair_finiteExponentialMultiplication S S M N T hT hF a c).2
  have hFD : 𝓕 D ∈ stronglyTemperedAtomicAtExponent K M := by
    have h := stronglyTemperedAtomicAtExponent_fourier_fourier K M U hUK
    simpa only [K, scaledTranslatedConeCarrier_zero_reflect] using h
  have hpair := stronglyTemperedOriginalPair_finiteTranslatedSymbolProduct
    (finiteCombConvolutionCarrier S a) K N M D hDS hFD a c r
  have hGK : G ∈ stronglyTemperedAtomicAtExponent (finiteCombConvolutionCarrier K a) N := by
    apply stronglyTemperedAtomicAtExponent_finiteTranslatedSymbolProduct_cleared
      (finiteCombConvolutionCarrier S a) (finiteCombConvolutionCarrier K a) N D hDS a c r
    intro x hx hn
    exact finiteRootClearingProduct_zero_outside_cone S K A a c hS hroot x hx hn
  have hG : G ∈ stronglyTemperedAtomicAtExponent (scaledTranslatedConeCarrier P Q scale hs) N :=
    stronglyTemperedAtomicAtExponent_mono_carrier
      (by simpa only [K, a, P, Q, zero_add] using
        finiteCombConvolutionCarrier_positive_cone_subset 0 0 scale hs p) N G hGK
  have hFG : 𝓕 G ∈ stronglyTemperedAtomicAtExponent
      (scaledTranslatedConeCarrier ((r.length : ℤ) * P) ((r.length : ℤ) * Q) scale hs) M :=
    stronglyTemperedAtomicAtExponent_mono_carrier
      (finiteTranslatedSymbolProductFourierCarrier_positive_cone_subset scale hs p r) M (𝓕 G) hpair.2
  exact originalStrong_two_cone_no_return P Q ((r.length : ℤ) * P) ((r.length : ℤ) * Q)
    m hm N M G hG hFG

end
end MeyerGeneralProblem.StrongParity
