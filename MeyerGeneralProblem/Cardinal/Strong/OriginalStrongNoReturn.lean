module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalNoReturnGeometry
public import MeyerGeneralProblem.Distribution.OriginalShrinkingFourierTest

@[expose] public section

/-!
# Strong two-cone no-return for the actual ORIGINAL records

Every distribution with both original strongly tempered records in two complete
translated cones at a literal private scale is zero. The proof uses a genuine
shrinking compact test, actual Fourier finite difference, global original TV
bound, literal Liouville decay, and internally proved quadratic return exclusion.
This theorem is specifically strong; it asserts no broad Hermite no-return.
-/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open Filter
open scoped FourierTransform

/-- Actual compact unit bump, fixed independently of all distributions and return indices. -/
def originalNoReturnBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- A genuine Schwartz test supported in the closed unit interval. -/
def originalNoReturnUnitTest : SchwartzMap ℝ ℂ :=
  by
    let f : ℝ → ℂ := Complex.ofRealCLM ∘ originalNoReturnBump
    have hf : HasCompactSupport f := originalNoReturnBump.hasCompactSupport.comp_left rfl
    exact hf.toSchwartzMap (Complex.ofRealCLM.contDiff.comp originalNoReturnBump.contDiff)

theorem originalNoReturnUnitTest_zero : originalNoReturnUnitTest 0 = 1 := by
  change (originalNoReturnBump 0 : ℂ) = 1
  rw [originalNoReturnBump.one_of_mem_closedBall (by simp [originalNoReturnBump])]
  norm_num

theorem originalNoReturnUnitTest_outside (x : ℝ) (hx : 1 ≤ |x|) :
    originalNoReturnUnitTest x = 0 := by
  change (originalNoReturnBump x : ℂ) = 0
  rw [originalNoReturnBump.zero_of_le_dist]
  · norm_num
  · simpa only [originalNoReturnBump, Real.dist_eq, sub_zero] using hx

/-- ALL actual shrinking-mask actions tend to zero under the original strong spectral record. -/
theorem originalStrong_quartic_mask_action_tendsto_zero (A B : ℤ) (scale : ℝ)
    (hs : 0 < scale) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (scaledTranslatedConeCarrier A B scale hs) N)
    (t : ℝ) (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => T (originalMaskSchwartzTest scale n
      (𝓕⁻ (originalQuarticShrinkingTest n t φ)))) atTop (nhds 0) := by
  let C : ℝ := 2 * Real.pi * originalMaskConeConstant A B scale *
    originalPointweightBound (N + 1) (𝓕⁻ φ) *
      ∑' x, stronglyTemperedCoefficientTerm (scaledTranslatedConeCarrier A B scale hs) N T x
  apply squeeze_zero_norm (a := fun n => C *
    ((denominator (n + 1) : ℝ) ^ (4 * N) * |originalMaskError n|))
  · intro n
    have h := originalStrong_mask_action_le A B scale hs N T hT n
      (𝓕⁻ (originalQuarticShrinkingTest n t φ))
      ((denominator (n + 1) : ℝ) ^ (4 * N) * originalPointweightBound (N + 1) (𝓕⁻ φ))
      (originalQuarticShrinkingTest_fourierInv_pointweight_le n t φ N)
    convert! h using 1
    dsimp [C]
    ring
  · simpa only [mul_zero] using (originalMaskError_polynomial_tendsto_zero (4 * N)).const_mul C

/-- Shrinking compact tests eventually read the SINGLE ORIGINAL coefficient at every atom. -/
theorem originalQuarticShrinkingTest_eventually_isolates (S : LocallyFiniteCarrier)
    (x : S.subtype) : ∀ᶠ n in atTop, ∀ y : S.subtype,
      originalQuarticShrinkingTest n x originalNoReturnUnitTest y = if y = x then 1 else 0 := by
  have hl : Tendsto (fun n => (denominator (n + 1) : ℝ) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 4 ≠ 0)).comp denominator_succ_tendsto_atTop
  filter_upwards [hl.eventually_ge_atTop ((S.isolationRadius x)⁻¹)] with n hn y
  have hb : 0 < (denominator (n + 1) : ℝ) ^ 4 := by
    have h := denominator_pos (n + 1); positivity
  rw [originalQuarticShrinkingTest, originalShrinkingTest_apply]
  by_cases hy : y = x
  · subst y
    simp only [sub_self, mul_zero, originalNoReturnUnitTest_zero, ↓reduceIte]
  · rw [ite_eq_right hy]
    apply originalNoReturnUnitTest_outside
    rw [abs_mul, abs_of_pos hb]
    have hdist := S.isolationRadius_le_dist x y.property
      (show (y : ℝ) ≠ x by exact fun he => hy (Subtype.ext he))
    have hrad := S.isolationRadius_pos x
    have hmult : 1 ≤ (denominator (n + 1) : ℝ) ^ 4 * S.isolationRadius x := by
      have h := mul_le_mul_of_nonneg_right hn hrad.le
      simpa only [inv_mul_cancel₀ hrad.ne'] using h
    rw [Real.dist_eq] at hdist
    exact hmult.trans (mul_le_mul_of_nonneg_left hdist hb.le)

/-- The translated shrinking test eventually vanishes at EVERY physical cone point. -/
theorem originalQuarticShrinkingTest_eventually_no_return (A B : ℤ) (m : ℕ) (hm : 0 < m)
    (x : (scaledTranslatedConeCarrier A B (originalPrivateScale m)
      (originalPrivateScale_pos m hm)).subtype) :
    ∀ᶠ n in atTop, ∀ y : (scaledTranslatedConeCarrier A B (originalPrivateScale m)
        (originalPrivateScale_pos m hm)).subtype,
      combSchwartzTranslation (originalPrivateScale m * (denominator (n + 1) : ℝ))
        (originalQuarticShrinkingTest n x originalNoReturnUnitTest) y = 0 := by
  obtain ⟨z, hz⟩ := scaledTranslatedConeCarrier_label A B (originalPrivateScale m)
    (originalPrivateScale_pos m hm) x
  filter_upwards [originalNoReturn_physical_window_empty A B m hm z] with n hn y
  obtain ⟨w, hw⟩ := scaledTranslatedConeCarrier_label A B (originalPrivateScale m)
    (originalPrivateScale_pos m hm) y
  rw [combSchwartzTranslation_apply, originalQuarticShrinkingTest, originalShrinkingTest_apply]
  apply originalNoReturnUnitTest_outside
  have hb : 0 < (denominator (n + 1) : ℝ) ^ 4 := by
    have h := denominator_pos (n + 1); positivity
  rw [abs_mul, abs_of_pos hb]
  have he : originalPrivateScale m * (denominator (n + 1) : ℝ) + (y : ℝ) - x =
      translatedConeFrequency A B w / originalPrivateScale m -
        (translatedConeFrequency A B z / originalPrivateScale m -
          originalPrivateScale m * (denominator (n + 1) : ℝ)) := by rw [hw, hz]; ring
  rw [he]
  simpa only [mul_comm] using (div_le_iff₀ hb).mp (hn w).le

/-- GENUINE strong no-return on two COMPLETE translated quadrants at the actual quartic scale.
The conclusion covers EVERY distribution with both ORIGINAL TV records, including all axes. -/
theorem originalStrong_two_cone_no_return (A B D E : ℤ) (m : ℕ) (hm : 0 < m)
    (M N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent
      (scaledTranslatedConeCarrier A B (originalPrivateScale m) (originalPrivateScale_pos m hm)) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent
      (scaledTranslatedConeCarrier D E (originalPrivateScale m) (originalPrivateScale_pos m hm)) N) :
    T = 0 := by
  let S := scaledTranslatedConeCarrier A B (originalPrivateScale m) (originalPrivateScale_pos m hm)
  apply locallyAtomic_eq_of_isolationAction_eq S T 0 hT.1
    ((stronglyTemperedAtomicAtExponent S M).zero_mem).1
  intro x
  have hlim := originalStrong_quartic_mask_action_tendsto_zero D E (originalPrivateScale m)
    (originalPrivateScale_pos m hm) N (𝓕 T) hF x originalNoReturnUnitTest
  have he : (fun n => (𝓕 T) (originalMaskSchwartzTest (originalPrivateScale m) n
      (𝓕⁻ (originalQuarticShrinkingTest n x originalNoReturnUnitTest)))) =ᶠ[atTop]
      fun _ => T (S.isolationSchwartz x) := by
    filter_upwards [originalQuarticShrinkingTest_eventually_isolates S x,
      originalQuarticShrinkingTest_eventually_no_return A B m hm x] with n hi hr
    rw [TemperedDistribution.fourier_apply, fourier_originalMaskSchwartzTest,
      FourierTransform.fourier_fourierInv_eq, map_sub]
    have hz : T (combSchwartzTranslation
        (originalPrivateScale m * (denominator (n + 1) : ℝ))
        (originalQuarticShrinkingTest n x originalNoReturnUnitTest)) = 0 := by
      rw [stronglyTemperedAtomicAtExponent_apply_tsum S M T hT]
      simp only [hr, mul_zero, tsum_zero]
    rw [hz, sub_zero, stronglyTemperedAtomicAtExponent_apply_tsum S M T hT, tsum_eq_single x]
    · rw [hi x, ite_eq_left rfl, mul_one]
    · intro y hy
      rw [hi y, ite_eq_right hy, mul_zero]
  have hc : T (S.isolationSchwartz x) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hlim.congr' he)
  simpa only [zero_apply] using hc

/-- The COMPLETE strong two-record space vanishes, with both exponents chosen by membership. -/
theorem originalStrong_complete_two_cone_no_return (A B D E : ℤ) (m : ℕ) (hm : 0 < m)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedAtomicOnCarrier
      (scaledTranslatedConeCarrier A B (originalPrivateScale m) (originalPrivateScale_pos m hm)))
    (hF : 𝓕 T ∈ StronglyTemperedAtomicOnCarrier
      (scaledTranslatedConeCarrier D E (originalPrivateScale m) (originalPrivateScale_pos m hm))) :
    T = 0 := by
  obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT
  obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hF
  exact originalStrong_two_cone_no_return A B D E m hm M N T hM hN

end
end MeyerGeneralProblem.StrongParity
