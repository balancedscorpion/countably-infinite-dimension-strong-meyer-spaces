module

public import MeyerGeneralProblem.Cardinal.Strong.ProductLaurentSupport
public import MeyerGeneralProblem.Cardinal.Strong.ProductReverseNumerator

@[expose] public section

/-! Every arbitrary original pair has its actual numerator in the complete
original finite Newton slab, including both signs and exclusion of the top corner. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped SchwartzMap FourierTransform

theorem spectralCone_integer_coordinate_signs {n : ℤ × ℤ}
    (hn : rankTwoFrequencyHom n ∈ spectralConeCarrier.carrier) :
    (0 ≤ n.1 ∧ 0 ≤ n.2) ∨ (n.1 ≤ 0 ∧ n.2 ≤ 0) := by
  obtain ⟨⟨b, k, j⟩, h⟩ := hn
  cases b
  · have heq : ((k : ℤ), (j : ℤ)) = n := by
      apply rankTwoFrequencyHom_injective
      simpa [rankTwoFrequencyHom_apply, signedConeFrequency, positiveConeFrequency] using h
    rw [← heq]
    exact Or.inl ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  · have heq : (-(k : ℤ), -(j : ℤ)) = n := by
      apply rankTwoFrequencyHom_injective
      simpa [rankTwoFrequencyHom_apply, signedConeFrequency, positiveConeFrequency, add_comm] using h
    rw [← heq]
    exact Or.inr ⟨neg_nonpos.mpr (Int.natCast_nonneg _), neg_nonpos.mpr (Int.natCast_nonneg _)⟩

theorem originalPositiveCut_coordinate_nonneg (T : TemperedDistribution ℝ ℂ) {n : ℤ × ℤ}
    (hn : arrayPositiveCut rankTwoFrequencyHom 0
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T) n ≠ 0) :
    0 ≤ n.1 ∧ 0 ≤ n.2 := by
  classical
  have hfreq : 0 ≤ rankTwoFrequencyHom n := by
    by_contra h
    exact hn (by dsimp only [arrayPositiveCut]; rw [ite_eq_right h])
  have hmem : rankTwoFrequencyHom n ∈ spectralConeCarrier.carrier := by
    by_contra h
    exact hn (by simp [arrayPositiveCut, originalFourierArray, extendedAtomicCoefficient, h])
  rcases spectralCone_integer_coordinate_signs hmem with hpos | hneg
  · exact hpos
  · have h₁ : (n.1 : ℝ) ≤ 0 := by exact_mod_cast hneg.1
    have h₂ : (n.2 : ℝ) ≤ 0 := by exact_mod_cast hneg.2
    have hb : 0 < beta := lt_trans (by norm_num) beta_between_three_four.1
    rw [rankTwoFrequencyHom_apply] at hfreq
    have hmul : beta * (n.2 : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le h₂
    constructor
    · exact_mod_cast (show (0 : ℝ) ≤ n.1 by linarith)
    · exact_mod_cast (show (0 : ℝ) ≤ n.2 by nlinarith)

theorem originalNegativeCut_coordinate_nonpos (T : TemperedDistribution ℝ ℂ) {n : ℤ × ℤ}
    (hn : arrayNegativeCut rankTwoFrequencyHom 0
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T) n ≠ 0) :
    n.1 ≤ 0 ∧ n.2 ≤ 0 := by
  classical
  have hfreq : rankTwoFrequencyHom n < 0 := by
    by_contra h
    exact hn (by dsimp only [arrayNegativeCut]; rw [ite_eq_right h])
  have hmem : rankTwoFrequencyHom n ∈ spectralConeCarrier.carrier := by
    by_contra h
    exact hn (by simp [arrayNegativeCut, originalFourierArray, extendedAtomicCoefficient, h])
  rcases spectralCone_integer_coordinate_signs hmem with hpos | hneg
  · have h₁ : (0 : ℝ) ≤ n.1 := by exact_mod_cast hpos.1
    have h₂ : (0 : ℝ) ≤ n.2 := by exact_mod_cast hpos.2
    have hb : 0 ≤ beta := le_trans (by norm_num) beta_between_three_four.1.le
    rw [rankTwoFrequencyHom_apply] at hfreq
    exact False.elim ((not_lt_of_ge (by positivity : (0 : ℝ) ≤ n.1 + beta * n.2)) hfreq)
  · exact hneg

/-- The original complete Newton slab is forced for an arbitrary actual pair;
the common cone zero occurs in the positive half-line exactly once. -/
theorem product_originalCutNumerator_support_slab (s : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (productSheetCarrier s) T)
    (hFT : AtomicOnCarrier spectralConeCarrier (𝓕 T)) {n : ℤ × ℤ}
    (hn : cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients s) 0
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T) n ≠ 0) :
    0 ≤ n.1 ∧ n.1 ≤ s ∧ 0 ≤ n.2 ∧ n.2 ≤ s ∧ n ≠ ((s : ℤ), (s : ℤ)) := by
  classical
  obtain ⟨m, hm, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hb := productLaurentCoefficients_support_box s hm
  have hpos := originalPositiveCut_coordinate_nonneg T (mul_ne_zero_iff.mp hterm).2
  have hc := product_originalFourierArray_annihilated s T hT hFT
  have hnneg : annihilatorArrayConvolution (productLaurentCoefficients s)
      (arrayNegativeCut rankTwoFrequencyHom 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T)) n ≠ 0 := by
    intro h
    exact hn (by rw [cutArrayNumerator_eq_negative _ _ _ _ hc, h, neg_zero])
  obtain ⟨m', hm', hterm'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnneg
  have hb' := productLaurentCoefficients_support_box s hm'
  have hneg := originalNegativeCut_coordinate_nonpos T (mul_ne_zero_iff.mp hterm').2
  simp only [Prod.fst_sub, Prod.snd_sub] at hpos hneg
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  intro heq
  have hf : ¬rankTwoFrequencyHom (n - m') < 0 := by
    rw [heq, rankTwoFrequencyHom_apply]
    have h₁ : (0 : ℝ) ≤ (s : ℤ) - m'.1 := by exact_mod_cast (show 0 ≤ (s : ℤ) - m'.1 by omega)
    have h₂ : (0 : ℝ) ≤ (s : ℤ) - m'.2 := by exact_mod_cast (show 0 ≤ (s : ℤ) - m'.2 by omega)
    have hb : 0 ≤ beta := le_trans (by norm_num) beta_between_three_four.1.le
    apply not_lt_of_ge
    change (0 : ℝ) ≤ ((s : ℤ) - m'.1 : ℤ) + beta * ((s : ℤ) - m'.2 : ℤ)
    simpa only [Int.cast_sub] using add_nonneg h₁ (mul_nonneg hb h₂)
  have hcut := (mul_ne_zero_iff.mp hterm').2
  exact hcut (by dsimp only [arrayNegativeCut]; rw [ite_eq_right hf])

end

end MeyerGeneralProblem.StrongParity
