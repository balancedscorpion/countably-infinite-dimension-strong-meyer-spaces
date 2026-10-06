module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixClearing

@[expose] public section

/-! The actual ORIGINAL Fourier coefficient array on the whole common module.
Its complete two-quadrant support and ALL exterior recurrence equations are
proved before rational reconstruction. No raw restriction is asserted to be a
Fourier pair; this is only the literal zero-extended original coefficient array. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The WHOLE signed native cone, including both axes and the origin. -/
def originalTwoQuadrantLabels : Set (ℤ × ℤ) :=
  {z | (0 ≤ z.1 ∧ 0 ≤ z.2) ∨ (z.1 ≤ 0 ∧ z.2 ≤ 0)}

/-- Exact whole native cone membership for EVERY original integer module label. -/
theorem originalScaledModuleFrequency_mem_zero_cone_iff (scale : ℝ) (hs : 0 < scale)
    (z : ℤ × ℤ) : originalScaledModuleFrequency scale z ∈
      (scaledTranslatedConeCarrier 0 0 scale hs).carrier ↔ z ∈ originalTwoQuadrantLabels := by
  have hnative : originalScaledModuleFrequency scale z ∈
      (scaledTranslatedConeCarrier 0 0 scale hs).carrier ↔
        rankTwoFrequencyHom z ∈ translatedConeSet 0 0 := by
    constructor
    · rintro ⟨y, hy, he⟩
      have hyz : y = rankTwoFrequencyHom z := by
        apply mul_left_cancel₀ (inv_ne_zero hs.ne')
        simpa only [originalScaledModuleFrequency, rankTwoFrequencyHom_apply,
          div_eq_mul_inv, mul_comm] using he
      exact hyz ▸ hy
    · intro hz
      refine ⟨rankTwoFrequencyHom z, hz, ?_⟩
      simp only [originalScaledModuleFrequency, rankTwoFrequencyHom_apply, div_eq_mul_inv, mul_comm]
  rw [hnative, translatedConeSet_iff]
  constructor
  · rintro ⟨p, q, he, hpq⟩
    have hz : z = (p, q) := rankTwoFrequencyHom_injective he
    simpa only [hz, originalTwoQuadrantLabels, Set.mem_setOf_eq] using hpq
  · intro hz
    exact ⟨z.1, z.2, rfl, hz⟩

/-- The literal ORIGINAL Fourier coefficient at EVERY common integer-module label. -/
def originalScheduledPrefixFourierArray (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ) (z : ℤ × ℤ) : ℂ :=
  extendedAtomicCoefficient (originalScheduledPrefixCarrier bound k) (𝓕 T)
    (originalScaledModuleFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z)

/-- EVERY exterior array row is truly zero, proved from whole support and coupled module exclusions. -/
theorem originalScheduledPrefixFourierArray_zero_outside_quadrants (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ) (z : ℤ × ℤ) (hz : z ∉ originalTwoQuadrantLabels) :
    originalScheduledPrefixFourierArray bound k T z = 0 := by
  have hn : originalScaledModuleFrequency
      (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z ∉
        (originalScheduledPrefixCarrier bound k).carrier := by
    intro hx
    have hcover := originalScheduledPrefixCarrier_subset_roots_union_cone bound k hx
    rcases hcover with hroot | hcone
    · exact originalScheduledPrefixRootSet_not_mem_module bound k _ hroot
        (originalScaledModuleFrequency_mem_rational_module _ (originalScheduledPrefixDenominator_pos bound k) z)
    · exact hz ((originalScaledModuleFrequency_mem_zero_cone_iff _
        (originalPrivateScale_pos _ (originalScheduledPrefixDenominator_pos bound k)) z).mp hcone)
  simp only [originalScheduledPrefixFourierArray, extendedAtomicCoefficient, dif_neg hn]

/-- The ORIGINAL supported two-quadrant array obeys recurrence on ALL labels before reconstruction. -/
theorem originalScheduledPrefixFourierArray_recurrence (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) (z : ℤ × ℤ) :
    ∑ i : OriginalScheduledPrefixMotif bound k,
      originalScheduledPrefixPolynomialCoefficient bound k i * originalScheduledPrefixFourierArray bound k T
        (z - originalPositivePolynomialIntegerCoordinates (originalScheduledPrefixPolynomialCoordinates bound k) i) = 0 :=
  originalScheduledPrefix_complete_strong_recurrence bound k T hT z

end
end MeyerGeneralProblem.StrongParity
