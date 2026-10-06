module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixIntegerArray

@[expose] public section

/-! Complete original two-quadrant numerator geometry at a positive common scale.
Both cuts and recurrence on ALL labels are load-bearing. The origin is retained
exactly once in the positive cut; the strict negative cut excludes the top corner.
The actual mixed array supplies these ordinary array inputs internally downstream. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The WHOLE positive cut of an original two-quadrant array uses only nonnegative coordinates. -/
theorem originalTwoQuadrantPositiveCut_coordinate_nonneg (scale : ℝ) (hs : 0 < scale)
    (u : (ℤ × ℤ) → ℂ) (hu : ∀ z, z ∉ originalTwoQuadrantLabels → u z = 0)
    {n : ℤ × ℤ} (hn : arrayPositiveCut (originalScaledModuleFrequencyHom scale) 0 u n ≠ 0) :
    0 ≤ n.1 ∧ 0 ≤ n.2 := by
  classical
  have hfreq : 0 ≤ originalScaledModuleFrequencyHom scale n := by
    by_contra h
    exact hn (by simp only [arrayPositiveCut, ite_eq_right h])
  have hmem : n ∈ originalTwoQuadrantLabels := by
    by_contra h
    exact hn (by simp [arrayPositiveCut, hu n h])
  have hnative : 0 ≤ rankTwoFrequencyHom n := by
    change 0 ≤ rankTwoFrequencyHom n / scale at hfreq
    simpa only [zero_mul] using (le_div_iff₀ hs).mp hfreq
  rcases hmem with hpos | hneg
  · exact hpos
  · have h₁ : (n.1 : ℝ) ≤ 0 := by exact_mod_cast hneg.1
    have h₂ : (n.2 : ℝ) ≤ 0 := by exact_mod_cast hneg.2
    have hb : 0 < beta := lt_trans (by norm_num) beta_between_three_four.1
    rw [rankTwoFrequencyHom_apply] at hnative
    have hmul : beta * (n.2 : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le h₂
    constructor
    · exact_mod_cast (show (0 : ℝ) ≤ n.1 by linarith)
    · exact_mod_cast (show (0 : ℝ) ≤ n.2 by nlinarith)

/-- The WHOLE strict negative cut uses only nonpositive coordinates. -/
theorem originalTwoQuadrantNegativeCut_coordinate_nonpos (scale : ℝ) (hs : 0 < scale)
    (u : (ℤ × ℤ) → ℂ) (hu : ∀ z, z ∉ originalTwoQuadrantLabels → u z = 0)
    {n : ℤ × ℤ} (hn : arrayNegativeCut (originalScaledModuleFrequencyHom scale) 0 u n ≠ 0) :
    n.1 ≤ 0 ∧ n.2 ≤ 0 := by
  classical
  have hfreq : originalScaledModuleFrequencyHom scale n < 0 := by
    by_contra h
    exact hn (by simp only [arrayNegativeCut, ite_eq_right h])
  have hmem : n ∈ originalTwoQuadrantLabels := by
    by_contra h
    exact hn (by simp [arrayNegativeCut, hu n h])
  have hnative : rankTwoFrequencyHom n < 0 := by
    change rankTwoFrequencyHom n / scale < 0 at hfreq
    simpa only [zero_mul] using (div_lt_iff₀ hs).mp hfreq
  rcases hmem with hpos | hneg
  · have h₁ : (0 : ℝ) ≤ n.1 := by exact_mod_cast hpos.1
    have h₂ : (0 : ℝ) ≤ n.2 := by exact_mod_cast hpos.2
    have hb : 0 ≤ beta := le_trans (by norm_num) beta_between_three_four.1.le
    rw [rankTwoFrequencyHom_apply] at hnative
    exact False.elim ((not_lt_of_ge (by positivity : (0 : ℝ) ≤ n.1 + beta * n.2)) hnative)
  · exact hneg

/-- Complete original box and omitted top corner follow from BOTH cut equations on ALL labels. -/
theorem originalTwoQuadrantCutNumerator_support_box (scale : ℝ) (hs : 0 < scale)
    (q : (ℤ × ℤ) →₀ ℂ) (S : ℕ)
    (hq : ∀ m ∈ q.support, 0 ≤ m.1 ∧ m.1 ≤ S ∧ 0 ≤ m.2 ∧ m.2 ≤ S)
    (u : (ℤ × ℤ) → ℂ) (hu : ∀ z, z ∉ originalTwoQuadrantLabels → u z = 0)
    (hconv : ∀ n, annihilatorArrayConvolution q u n = 0) {n : ℤ × ℤ}
    (hn : cutArrayNumerator (originalScaledModuleFrequencyHom scale) q 0 u n ≠ 0) :
    0 ≤ n.1 ∧ n.1 ≤ S ∧ 0 ≤ n.2 ∧ n.2 ≤ S ∧ n ≠ ((S : ℤ), (S : ℤ)) := by
  classical
  obtain ⟨m, hm, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hb := hq m hm
  have hpos := originalTwoQuadrantPositiveCut_coordinate_nonneg scale hs u hu (mul_ne_zero_iff.mp hterm).2
  have hnneg : annihilatorArrayConvolution q
      (arrayNegativeCut (originalScaledModuleFrequencyHom scale) 0 u) n ≠ 0 := by
    intro h
    exact hn (by rw [cutArrayNumerator_eq_negative _ _ _ _ hconv, h, neg_zero])
  obtain ⟨m', hm', hterm'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnneg
  have hb' := hq m' hm'
  have hneg := originalTwoQuadrantNegativeCut_coordinate_nonpos scale hs u hu (mul_ne_zero_iff.mp hterm').2
  simp only [Prod.fst_sub, Prod.snd_sub] at hpos hneg
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  intro heq
  have hf : ¬originalScaledModuleFrequencyHom scale (n - m') < 0 := by
    rw [heq]
    have h₁ : (0 : ℝ) ≤ (S : ℤ) - m'.1 := by exact_mod_cast (show 0 ≤ (S : ℤ) - m'.1 by omega)
    have h₂ : (0 : ℝ) ≤ (S : ℤ) - m'.2 := by exact_mod_cast (show 0 ≤ (S : ℤ) - m'.2 by omega)
    have hb : 0 ≤ beta := le_trans (by norm_num) beta_between_three_four.1.le
    apply not_lt_of_ge
    change (0 : ℝ) ≤ (((S : ℤ) - m'.1 : ℤ) + beta * ((S : ℤ) - m'.2 : ℤ)) / scale
    apply div_nonneg _ hs.le
    simpa only [Int.cast_sub] using add_nonneg h₁ (mul_nonneg hb h₂)
  have hcut := (mul_ne_zero_iff.mp hterm').2
  exact hcut (by simp only [arrayNegativeCut, ite_eq_right hf])

/-- The actual whole integer numerator box, with the top corner omitted. -/
def originalTwoQuadrantNumeratorBox (S : ℕ) : Set (ℤ × ℤ) :=
  {n | 0 ≤ n.1 ∧ n.1 ≤ S ∧ 0 ≤ n.2 ∧ n.2 ≤ S ∧ n ≠ ((S : ℤ), (S : ℤ))}

/-- Finiteness of the whole numerator box is supplied by actual integer interval finiteness. -/
theorem originalTwoQuadrantNumeratorBox_finite (S : ℕ) : (originalTwoQuadrantNumeratorBox S).Finite := by
  apply ((Set.finite_Icc (0 : ℤ) (S : ℤ)).prod (Set.finite_Icc (0 : ℤ) (S : ℤ))).subset
  intro n hn
  exact ⟨⟨hn.1, hn.2.1⟩, hn.2.2.1, hn.2.2.2.1⟩

end
end MeyerGeneralProblem.StrongParity
