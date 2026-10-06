module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalStrongRootClearing

@[expose] public section

/-!
# Original all-module-label recurrence from TRUE strong zero-output clearing

The actual g_+*F(f*T)=0 theorem removes the original Fourier-convolution
coefficient at every point where the literal product is nonzero. For ordinary
positive native polynomial data avoiding the native module, this yields the
recurrence on ALL integer labels, including every exterior quadrant label.
No chosen forward source, restricted Fourier pair or cleared-output certificate
is a premise. The actual mixed-prefix polynomial specialization remains separate.
-/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- Literal frequency of EVERY native integer module label at an ordinary positive scale. -/
def originalScaledModuleFrequency (scale : ℝ) (z : ℤ × ℤ) : ℝ :=
  ((z.1 : ℝ) + beta * (z.2 : ℝ)) / scale

/-- Exact positive native polynomial coordinates as original integer labels. -/
def originalPositivePolynomialIntegerCoordinates {ι : Type*} (p : ι → ℕ × ℕ) (i : ι) : ℤ × ℤ :=
  ((p i).1, (p i).2)

/-- Exact frequency subtraction on the WHOLE original integer module. -/
theorem originalScaledModuleFrequency_sub_positive {ι : Type*}
    (scale : ℝ) (z : ℤ × ℤ) (p : ι → ℕ × ℕ) (i : ι) :
    originalScaledModuleFrequency scale z - originalPositivePolynomialFrequency scale p i =
      originalScaledModuleFrequency scale (z - originalPositivePolynomialIntegerCoordinates p i) := by
  simp only [originalScaledModuleFrequency, originalPositivePolynomialFrequency,
    originalPositivePolynomialIntegerCoordinates, positiveConeFrequency,
    Prod.fst_sub, Prod.snd_sub, Int.cast_sub, Int.cast_natCast]
  ring

/-- Nonvanishing on the actual module supplies EVERY clearing-factor nonvanishing internally. -/
theorem finiteRootClearingProduct_nonzero_on_module {ι : Type*} [Fintype ι]
    (scale : ℝ) (p : ι → ℕ × ℕ) (c : ι → ℂ)
    (havoid : ∀ z : ℤ × ℤ, finitePositiveExponentialSymbol
      (originalPositivePolynomialFrequency scale p) c (originalScaledModuleFrequency scale z) ≠ 0)
    (z : ℤ × ℤ) : finiteTranslatedSymbolProductValue
      (originalPositivePolynomialFrequency scale p) c
      (finiteRootClearingShifts (originalPositivePolynomialFrequency scale p))
      (originalScaledModuleFrequency scale z) ≠ 0 := by
  classical
  unfold finiteTranslatedSymbolProductValue
  apply List.prod_ne_zero
  intro hv
  obtain ⟨r, hr, he⟩ := List.mem_map.mp hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  rw [originalScaledModuleFrequency_sub_positive] at he
  exact havoid _ he

/-- TRUE zero-output clearing gives the exact original finite-shift recurrence at any
nonvanishing clearing point, including points outside the original support. -/
theorem originalStrongClearing_original_point_recurrence {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (A : Set ℝ) (m : ℕ) (hm : 0 < m)
    (p : ι → ℕ × ℕ) (c : ι → ℂ)
    (hS : S.carrier ⊆ A ∪ (scaledTranslatedConeCarrier 0 0 (originalPrivateScale m)
      (originalPrivateScale_pos m hm)).carrier)
    (hroot : ∀ x ∈ A, finitePositiveExponentialSymbol
      (originalPositivePolynomialFrequency (originalPrivateScale m) p) c x = 0)
    (M N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N)
    (x : ℝ) (hx : finiteTranslatedSymbolProductValue
      (originalPositivePolynomialFrequency (originalPrivateScale m) p) c
      (finiteRootClearingShifts (originalPositivePolynomialFrequency (originalPrivateScale m) p)) x ≠ 0) :
    ∑ i, c i * extendedAtomicCoefficient S (𝓕 T)
      (x - originalPositivePolynomialFrequency (originalPrivateScale m) p i) = 0 := by
  classical
  let a := originalPositivePolynomialFrequency (originalPrivateScale m) p
  let r := finiteRootClearingShifts a
  let U := finiteCombConvolutionCarrier S a
  let D := 𝓕 (finiteExponentialMultiplication a c T)
  have hD : D ∈ stronglyTemperedAtomicAtExponent U N :=
    (stronglyTemperedOriginalPair_finiteExponentialMultiplication S S M N T hT hF a c).2
  have hG : finiteTranslatedSymbolProduct a c r D = 0 :=
    originalStrongRootClearedFourierDistribution_eq_zero S A m hm p c hS hroot M N T hT hF
  have he : extendedAtomicCoefficient U D x = 0 := by
    unfold extendedAtomicCoefficient
    split_ifs with hxu
    · have hc := finiteTranslatedSymbolProduct_isolation_apply U N D hD a c r ⟨x, hxu⟩
      rw [hG, zero_apply] at hc
      exact (mul_eq_zero.mp hc.symm).resolve_left hx
    · rfl
  have hdEq : D = finiteCombConvolution a c (𝓕 T) := fourier_finiteExponentialMultiplication a c T
  rw [hdEq, extendedAtomicCoefficient_finiteCombConvolution S (𝓕 T)
    (hasLocallyAtomicAction_atomicOnCarrier S (𝓕 T) hF.1) a c x] at he
  exact he

/-- ALL original Fourier module labels satisfy the finite polynomial recurrence,
including exterior labels BEFORE any cone restriction or rational reconstruction. -/
theorem originalStrongClearing_all_integer_label_recurrence {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (A : Set ℝ) (m : ℕ) (hm : 0 < m)
    (p : ι → ℕ × ℕ) (c : ι → ℂ)
    (hS : S.carrier ⊆ A ∪ (scaledTranslatedConeCarrier 0 0 (originalPrivateScale m)
      (originalPrivateScale_pos m hm)).carrier)
    (hroot : ∀ x ∈ A, finitePositiveExponentialSymbol
      (originalPositivePolynomialFrequency (originalPrivateScale m) p) c x = 0)
    (havoid : ∀ z : ℤ × ℤ, finitePositiveExponentialSymbol
      (originalPositivePolynomialFrequency (originalPrivateScale m) p) c
        (originalScaledModuleFrequency (originalPrivateScale m) z) ≠ 0)
    (M N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) (z : ℤ × ℤ) :
    ∑ i, c i * extendedAtomicCoefficient S (𝓕 T)
      (originalScaledModuleFrequency (originalPrivateScale m)
        (z - originalPositivePolynomialIntegerCoordinates p i)) = 0 := by
  have h := originalStrongClearing_original_point_recurrence S A m hm p c hS hroot M N T hT hF
    (originalScaledModuleFrequency (originalPrivateScale m) z)
    (finiteRootClearingProduct_nonzero_on_module (originalPrivateScale m) p c havoid z)
  simpa only [originalScaledModuleFrequency_sub_positive] using h

end
end MeyerGeneralProblem.StrongParity
