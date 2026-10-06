module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalRootAnchors

@[expose] public section

/-! The finite projection built from the ACTUAL original root anchor tests.
Both complete original records supply its coefficients. Its action on every
native and inverse Fourier mode is proved internally. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- Actual finite root-anchor projection using BOTH whole original records. -/
def originalScheduledAnchorProjection (bound : ℕ → ℕ) (r : ℕ)
    (T : TemperedDistribution ℝ ℂ) : TemperedDistribution ℝ ℂ :=
  (∑ i : Fin r, T (originalScheduledPrefixAnchorTest bound r i) •
    originalScheduledPrivateLineSource bound i.val) +
  𝓕⁻ (∑ i : Fin r, 𝓕 T (originalScheduledPrefixAnchorTest bound r i) •
    originalScheduledPrivateLineSource bound i.val)

/-- The actual projection is additive on full tempered distributions. -/
theorem originalScheduledAnchorProjection_add (bound : ℕ → ℕ) (r : ℕ)
    (T U : TemperedDistribution ℝ ℂ) :
    originalScheduledAnchorProjection bound r (T + U) =
      originalScheduledAnchorProjection bound r T + originalScheduledAnchorProjection bound r U := by
  have hs (a b : Fin r → ℂ) :
      (∑ i : Fin r, (a i + b i) • originalScheduledPrivateLineSource bound i.val) =
        (∑ i : Fin r, a i • originalScheduledPrivateLineSource bound i.val) +
          ∑ i : Fin r, b i • originalScheduledPrivateLineSource bound i.val := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact add_smul (a i) (b i) (originalScheduledPrivateLineSource bound i.val)
  change (∑ i : Fin r, (T (originalScheduledPrefixAnchorTest bound r i) +
      U (originalScheduledPrefixAnchorTest bound r i)) • originalScheduledPrivateLineSource bound i.val) +
    𝓕⁻ (∑ i : Fin r, (𝓕 T (originalScheduledPrefixAnchorTest bound r i) +
      𝓕 U (originalScheduledPrefixAnchorTest bound r i)) • originalScheduledPrivateLineSource bound i.val) = _
  rw [hs, hs, FourierTransform.fourierInv_add]
  unfold originalScheduledAnchorProjection
  abel

/-- The actual projection is complex linear, including its genuine Fourier inverse part. -/
theorem originalScheduledAnchorProjection_smul (bound : ℕ → ℕ) (r : ℕ)
    (c : ℂ) (T : TemperedDistribution ℝ ℂ) :
    originalScheduledAnchorProjection bound r (c • T) = c • originalScheduledAnchorProjection bound r T := by
  simp only [originalScheduledAnchorProjection, FourierTransform.fourier_smul, smul_apply,
    smul_eq_mul, mul_smul, ← Finset.smul_sum, FourierTransform.fourierInv_smul, smul_add]

/-- The ACTUAL constructed root-anchor operator as a complex linear map. -/
def originalScheduledAnchorProjectionLinearMap (bound : ℕ → ℕ) (r : ℕ) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toFun := originalScheduledAnchorProjection bound r
  map_add' := originalScheduledAnchorProjection_add bound r
  map_smul' := originalScheduledAnchorProjection_smul bound r

/-- The actual projection fixes EVERY selected native mode. -/
theorem originalScheduledAnchorProjection_native (bound : ℕ → ℕ) (r : ℕ) (j : Fin r) :
    originalScheduledAnchorProjection bound r (originalScheduledPrivateLineSource bound j.val) =
      originalScheduledPrivateLineSource bound j.val := by
  classical
  simp only [originalScheduledAnchorProjection, originalScheduledPrefixAnchorTest_native,
    originalScheduledPrefixAnchorTest_native_fourier]
  generalize originalScheduledPrivateLineSource bound = v
  have hz (t : TemperedDistribution ℝ ℂ) : (0 : ℂ) • t = 0 := zero_smul ℂ t
  simp only [ite_smul, one_smul, hz, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.sum_const_zero, FourierTransform.fourierInv_zero, add_zero]

/-- The SAME actual projection fixes EVERY selected genuine inverse Fourier mode. -/
theorem originalScheduledAnchorProjection_inverse (bound : ℕ → ℕ) (r : ℕ) (j : Fin r) :
    originalScheduledAnchorProjection bound r (𝓕⁻ (originalScheduledPrivateLineSource bound j.val)) =
      𝓕⁻ (originalScheduledPrivateLineSource bound j.val) := by
  classical
  simp only [originalScheduledAnchorProjection, originalScheduledPrefixAnchorTest_inverse,
    FourierTransform.fourier_fourierInv_eq, originalScheduledPrefixAnchorTest_native]
  generalize originalScheduledPrivateLineSource bound = v
  have hz (t : TemperedDistribution ℝ ℂ) : (0 : ℂ) • t = 0 := zero_smul ℂ t
  simp only [ite_smul, one_smul, hz, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.sum_const_zero, zero_add]

/-- The actual projection fixes every finite mixed combination of its original modes. -/
theorem originalScheduledAnchorProjection_mixed_sum (bound : ℕ → ℕ) (r : ℕ) (a b : Fin r → ℂ) :
    originalScheduledAnchorProjection bound r
      ((∑ i : Fin r, a i • originalScheduledPrivateLineSource bound i.val) +
        𝓕⁻ (∑ i : Fin r, b i • originalScheduledPrivateLineSource bound i.val)) =
      (∑ i : Fin r, a i • originalScheduledPrivateLineSource bound i.val) +
        𝓕⁻ (∑ i : Fin r, b i • originalScheduledPrivateLineSource bound i.val) := by
  change originalScheduledAnchorProjectionLinearMap bound r _ = _
  rw [map_add]
  have hi : 𝓕⁻ (∑ i : Fin r, b i • originalScheduledPrivateLineSource bound i.val) =
      ∑ i : Fin r, b i • 𝓕⁻ (originalScheduledPrivateLineSource bound i.val) := by
    rw [FourierTransform.fourierInv_sum]
    simp only [FourierTransform.fourierInv_smul]
  rw [hi, map_sum, map_sum]
  simp only [map_smul]
  change (∑ i : Fin r, a i • originalScheduledAnchorProjection bound r
    (originalScheduledPrivateLineSource bound i.val)) +
    (∑ i : Fin r, b i • originalScheduledAnchorProjection bound r
      (𝓕⁻ (originalScheduledPrivateLineSource bound i.val))) = _
  simp only [originalScheduledAnchorProjection_native, originalScheduledAnchorProjection_inverse]

/-- Every complete original finite-prefix strong source is fixed, with NO projection certificate. -/
theorem originalScheduledAnchorProjection_complete_prefix (bound : ℕ → ℕ) (r : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound r)) :
    originalScheduledAnchorProjection bound r T = T := by
  obtain ⟨a, b, rfl⟩ := originalScheduledPrefix_complete_mixed_private_lines bound r T hT
  exact originalScheduledAnchorProjection_mixed_sum bound r a b

end
end MeyerGeneralProblem.StrongParity
