module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductAnnihilator
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductLaurentSupport
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductReverseNumerator
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductNumeratorSlab

@[expose] public section

/-! Complete original ProductNumeratorSlab for actual compact parameter blocks.
Every original supported pair is retained, without a constructed-image premise. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open scoped SchwartzMap FourierTransform

/-- The original complete Newton slab is forced for an arbitrary actual pair;
the common cone zero occurs in the positive half-line exactly once. -/
theorem product_originalCutNumerator_support_slab {s : ℕ} (block : CompactOriginalParameterBlock s) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (compactOriginalProductSheetCarrier block) T)
    (hFT : AtomicOnCarrier spectralConeCarrier (𝓕 T)) {n : ℤ × ℤ}
    (hn : cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients block) 0
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T) n ≠ 0) :
    0 ≤ n.1 ∧ n.1 ≤ s ∧ 0 ≤ n.2 ∧ n.2 ≤ s ∧ n ≠ ((s : ℤ), (s : ℤ)) := by
  classical
  obtain ⟨m, hm, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hb := productLaurentCoefficients_support_box block hm
  have hpos := originalPositiveCut_coordinate_nonneg T (mul_ne_zero_iff.mp hterm).2
  have hc := product_originalFourierArray_annihilated block T hT hFT
  have hnneg : annihilatorArrayConvolution (productLaurentCoefficients block)
      (arrayNegativeCut rankTwoFrequencyHom 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T)) n ≠ 0 := by
    intro h
    exact hn (by rw [cutArrayNumerator_eq_negative _ _ _ _ hc, h, neg_zero])
  obtain ⟨m', hm', hterm'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnneg
  have hb' := productLaurentCoefficients_support_box block hm'
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

end MeyerGeneralProblem.StrongParity.CompactOriginal
