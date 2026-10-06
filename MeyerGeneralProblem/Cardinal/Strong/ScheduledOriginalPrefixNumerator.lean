module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalTwoQuadrantNumerator
public import MeyerGeneralProblem.Cardinal.Strong.OriginalPairNumerator

@[expose] public section

/-! The genuine finite cut numerator of EVERY complete original mixed-prefix
strong pair. All coefficient, support, frequency and recurrence inputs are supplied
internally. Equality determines the WHOLE original module array; reconstruction of
the distribution at the extra physical root labels remains a separate obligation. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual original cut numerator is finitely supported inside the whole mixed box. -/
theorem originalScheduledPrefixCutNumerator_support_finite (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    (Function.support (cutArrayNumerator
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
      (originalScheduledPrefixIntegerCoefficients bound k) 0
      (originalScheduledPrefixFourierArray bound k T))).Finite := by
  apply (originalTwoQuadrantNumeratorBox_finite (originalScheduledPrefixPolynomialDegree bound k)).subset
  intro n hn
  exact originalTwoQuadrantCutNumerator_support_box _
    (originalPrivateScale_pos _ (originalScheduledPrefixDenominator_pos bound k)) _ _
    (fun _ hm => originalScheduledPrefixIntegerCoefficients_support_box bound k hm) _
    (originalScheduledPrefixFourierArray_zero_outside_quadrants bound k T)
    (originalScheduledPrefixIntegerArray_annihilated bound k T hT) hn

/-- The finite numerator is the literal convolution of the original positive cut. -/
def originalScheduledPrefixNumerator (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) : (ℤ × ℤ) →₀ ℂ :=
  Finsupp.ofSupportFinite
    (cutArrayNumerator
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
      (originalScheduledPrefixIntegerCoefficients bound k) 0 (originalScheduledPrefixFourierArray bound k T))
    (originalScheduledPrefixCutNumerator_support_finite bound k T hT)

/-- Every coefficient is the exact original cut numerator, including all exterior labels. -/
theorem originalScheduledPrefixNumerator_apply (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (n : ℤ × ℤ) :
    originalScheduledPrefixNumerator bound k T hT n = cutArrayNumerator
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
      (originalScheduledPrefixIntegerCoefficients bound k) 0 (originalScheduledPrefixFourierArray bound k T) n := rfl

/-- The positive formula retains zero exactly once and holds on ALL original labels. -/
theorem originalScheduledPrefixNumerator_positive (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (n : ℤ × ℤ) :
    originalScheduledPrefixNumerator bound k T hT n = annihilatorArrayConvolution
      (originalScheduledPrefixIntegerCoefficients bound k)
      (arrayPositiveCut
        (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
        0 (originalScheduledPrefixFourierArray bound k T)) n := rfl

/-- The strict negative formula is proved from the ALL-label original recurrence. -/
theorem originalScheduledPrefixNumerator_negative (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (n : ℤ × ℤ) :
    originalScheduledPrefixNumerator bound k T hT n = -annihilatorArrayConvolution
      (originalScheduledPrefixIntegerCoefficients bound k)
      (arrayNegativeCut
        (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
        0 (originalScheduledPrefixFourierArray bound k T)) n :=
  cutArrayNumerator_eq_negative _ _ _ _ (originalScheduledPrefixIntegerArray_annihilated bound k T hT) n

/-- The actual finite mixed numerator lies in the complete box with its top corner omitted. -/
theorem originalScheduledPrefixNumerator_support_box (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) {n : ℤ × ℤ}
    (hn : n ∈ (originalScheduledPrefixNumerator bound k T hT).support) :
    n ∈ originalTwoQuadrantNumeratorBox (originalScheduledPrefixPolynomialDegree bound k) := by
  apply originalTwoQuadrantCutNumerator_support_box _
    (originalPrivateScale_pos _ (originalScheduledPrefixDenominator_pos bound k)) _ _
    (fun _ hm => originalScheduledPrefixIntegerCoefficients_support_box bound k hm) _
    (originalScheduledPrefixFourierArray_zero_outside_quadrants bound k T)
    (originalScheduledPrefixIntegerArray_annihilated bound k T hT)
  exact Finsupp.mem_support_iff.mp hn

/-- Equality of genuine finite numerators determines EVERY original module coefficient. -/
theorem originalScheduledPrefixNumerator_determines_original_array (bound : ℕ → ℕ) (k : ℕ)
    (T U : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (hU : U ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (heq : originalScheduledPrefixNumerator bound k T hT = originalScheduledPrefixNumerator bound k U hU) :
    originalScheduledPrefixFourierArray bound k T = originalScheduledPrefixFourierArray bound k U := by
  let L := originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k))
  let q := originalScheduledPrefixIntegerCoefficients bound k
  have hL : Function.Injective L := originalScaledModuleFrequencyHom_injective _
    (originalPrivateScale_pos _ (originalScheduledPrefixDenominator_pos bound k)).ne'
  obtain ⟨m₀, m₁, hm₀, hm₁, _, hmin, hmax⟩ :=
    finiteAnnihilator_extrema L hL q (originalScheduledPrefixIntegerCoefficients_ne_zero bound k)
  apply cutArrayNumerator_injective_on_kernel L q m₀ m₁ hm₀ hm₁ hmin hmax 0 _ _
    (originalScheduledPrefixFourierArray_frequencyLocallyFinite bound k T)
    (originalScheduledPrefixFourierArray_frequencyLocallyFinite bound k U)
    (originalScheduledPrefixIntegerArray_annihilated bound k T hT)
    (originalScheduledPrefixIntegerArray_annihilated bound k U hU)
  funext n
  exact congrArg (fun R : (ℤ × ℤ) →₀ ℂ => R n) heq

/-- The empty prefix has degree zero, so its genuine box numerator is zero. -/
theorem originalScheduledPrefixNumerator_empty (bound : ℕ → ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound 0)) :
    originalScheduledPrefixNumerator bound 0 T hT = 0 := by
  classical
  ext n
  by_contra hn
  have hb := originalScheduledPrefixNumerator_support_box bound 0 T hT (Finsupp.mem_support_iff.mpr hn)
  simp only [originalTwoQuadrantNumeratorBox, originalScheduledPrefixPolynomialDegree,
    Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, Set.mem_ofPred_eq] at hb
  have heq : n = (0, 0) := Prod.ext (le_antisymm hb.2.1 hb.1) (le_antisymm hb.2.2.2.1 hb.2.2.1)
  exact hb.2.2.2.2 heq

end
end MeyerGeneralProblem.StrongParity
