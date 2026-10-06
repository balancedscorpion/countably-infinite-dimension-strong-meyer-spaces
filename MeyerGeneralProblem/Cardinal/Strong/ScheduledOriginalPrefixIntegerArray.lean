module

public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalPolynomialSupport
public import MeyerGeneralProblem.Cardinal.Strong.OriginalPositiveIntegerCoefficients

@[expose] public section

/-! The exact ACTUAL mixed-prefix Laurent coefficients and original array.
Its common frequency map is injective, original frequency local finiteness is
supplied internally, and whole-lattice convolution follows from ALL actual
exterior equations. No root-only Fourier pair or raw restriction is assumed. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- Actual additive frequency map on the WHOLE common integer module. -/
def originalScaledModuleFrequencyHom (scale : ℝ) : (ℤ × ℤ) →+ ℝ where
  toFun := originalScaledModuleFrequency scale
  map_zero' := by simp [originalScaledModuleFrequency]
  map_add' a b := by
    simp only [originalScaledModuleFrequency, Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring

/-- The common frequency homomorphism retains the literal geometric value. -/
theorem originalScaledModuleFrequencyHom_apply (scale : ℝ) (z : ℤ × ℤ) :
    originalScaledModuleFrequencyHom scale z = originalScaledModuleFrequency scale z := rfl

/-- Every nonzero common scale preserves exact injectivity of the original irrational module. -/
theorem originalScaledModuleFrequencyHom_injective (scale : ℝ) (hs : scale ≠ 0) :
    Function.Injective (originalScaledModuleFrequencyHom scale) := by
  intro p q h
  apply rankTwoFrequencyHom_injective
  apply mul_right_cancel₀ (inv_ne_zero hs)
  change rankTwoFrequencyHom p / scale = rankTwoFrequencyHom q / scale at h
  simpa only [div_eq_mul_inv] using h

/-- Exact unaltered whole integer coefficients of the complete actual mixed product. -/
def originalScheduledPrefixIntegerCoefficients (bound : ℕ → ℕ) (k : ℕ) : (ℤ × ℤ) →₀ ℂ :=
  originalPositivePolynomialIntegerCoefficients (originalScheduledPrefixPolynomial bound k)

/-- The genuine complete mixed annihilator is nonzero at its actual integer labels. -/
theorem originalScheduledPrefixIntegerCoefficients_ne_zero (bound : ℕ → ℕ) (k : ℕ) :
    originalScheduledPrefixIntegerCoefficients bound k ≠ 0 :=
  originalPositivePolynomialIntegerCoefficients_ne_zero _ (originalScheduledPrefixPolynomial_ne_zero bound k)

/-- Actual lifted mixed coefficients have the internally proved complete common box. -/
theorem originalScheduledPrefixIntegerCoefficients_support_box (bound : ℕ → ℕ) (k : ℕ)
    {n : ℤ × ℤ} (hn : n ∈ (originalScheduledPrefixIntegerCoefficients bound k).support) :
    0 ≤ n.1 ∧ n.1 ≤ originalScheduledPrefixPolynomialDegree bound k ∧
      0 ≤ n.2 ∧ n.2 ≤ originalScheduledPrefixPolynomialDegree bound k := by
  rw [originalScheduledPrefixIntegerCoefficients, originalPositivePolynomialIntegerCoefficients_support] at hn
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hn
  have hb := originalScheduledPrefixPolynomial_support_box bound k hp
  refine ⟨Int.natCast_nonneg p.1, ?_, Int.natCast_nonneg p.2, ?_⟩
  · change (p.1 : ℤ) ≤ (originalScheduledPrefixPolynomialDegree bound k : ℤ)
    exact_mod_cast hb.1
  · change (p.2 : ℤ) ≤ (originalScheduledPrefixPolynomialDegree bound k : ℤ)
    exact_mod_cast hb.2

/-- EVERY original array inherits actual frequency local finiteness from the whole finite carrier. -/
theorem originalScheduledPrefixFourierArray_frequencyLocallyFinite (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ) : FrequencyLocallyFinite
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
      (originalScheduledPrefixFourierArray bound k T) :=
  originalFourierArray_frequencyLocallyFinite _
    (originalScaledModuleFrequencyHom_injective _
      (originalPrivateScale_pos _ (originalScheduledPrefixDenominator_pos bound k)).ne')
    (originalScheduledPrefixCarrier bound k) T

/-- ALL original labels satisfy actual mixed Laurent convolution, including EVERY exterior label. -/
theorem originalScheduledPrefixIntegerArray_annihilated (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∀ n, annihilatorArrayConvolution (originalScheduledPrefixIntegerCoefficients bound k)
      (originalScheduledPrefixFourierArray bound k T) n = 0 := by
  intro n
  rw [originalScheduledPrefixIntegerCoefficients, originalPositivePolynomialIntegerCoefficients_convolution]
  exact originalScheduledPrefixFourierArray_recurrence bound k T hT n

end
end MeyerGeneralProblem.StrongParity
