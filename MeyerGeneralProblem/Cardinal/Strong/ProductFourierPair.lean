module

public import MeyerGeneralProblem.Cardinal.Strong.NonPoleProductJump
public import MeyerGeneralProblem.Cardinal.Adaptive.DistributionLocality

@[expose] public section

/-! Actual Fourier compatibility of EVERY complete original numerator slab.
Local integrated jumps are composed by the existing finite smooth partition
and actual compact Schwartz density. No Fourier certificate is assumed. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open Filter Set
open scoped Topology FourierTransform

/-- The literal difference between the actual inverse spectral record and
the actual original physical record. -/
def productFourierDefect (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    TemperedDistribution ℝ ℂ :=
  𝓕⁻ (productSpectralDistribution s r) - productPhysicalDistribution s r

/-- The complete original Fourier defect vanishes on a genuine open
neighborhood of EVERY real point, including every original pole. -/
theorem productFourierDefect_locally_vanishes (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : ℝ) : ∃ O : Set ℝ, IsOpen O ∧ x ∈ O ∧
      Adaptive.DistributionVanishesOn O (productFourierDefect s r) := by
  classical
  by_cases hx : x ∈ (productSheetCarrier s).carrier
  · let a : (productSheetCarrier s).subtype := ⟨x, hx⟩
    obtain ⟨δ, hδ, hlocal⟩ := productSpectral_fourierInv_local_root s r a
    let O : Set ℝ := Metric.ball x δ ∩
      Metric.ball x ((productSheetCarrier s).isolationRadius a)
    refine ⟨O, Metric.isOpen_ball.inter Metric.isOpen_ball,
      ⟨Metric.mem_ball_self hδ, Metric.mem_ball_self
        ((productSheetCarrier s).isolationRadius_pos a)⟩, ?_⟩
    intro f _ hsupport
    have hbound : ∀ y : ℝ, f y ≠ 0 → |y - (a : ℝ)| ≤ δ := by
      intro y hy
      have hball := (hsupport (subset_tsupport f hy)).1
      exact (by simpa only [Metric.mem_ball, Real.dist_eq] using hball : |y - x| < δ).le
    have hphys : productPhysicalDistribution s r f = productPhysicalResidue s r a * f a := by
      rw [productPhysicalDistribution_apply, tsum_eq_single a]
      intro b hb
      have hb0 : f b = 0 := by
        by_contra hnot
        have hball := (hsupport (subset_tsupport f hnot)).2
        have hdist : dist (b : ℝ) (a : ℝ) <
            (productSheetCarrier s).isolationRadius a := hball
        have hsep := (productSheetCarrier s).isolationRadius_le_dist a b.property
          (fun h => hb (Subtype.ext h))
        exact (not_lt_of_ge hsep) hdist
      rw [hb0, mul_zero]
    change (𝓕⁻ (productSpectralDistribution s r)) f - productPhysicalDistribution s r f = 0
    rw [hlocal f hbound, hphys, sub_self]
  · obtain ⟨δ, hδ, hlocal⟩ := productSpectral_fourierInv_local_nonpole s r x hx
    let O : Set ℝ := Metric.ball x δ ∩ (productSheetCarrier s).carrierᶜ
    refine ⟨O, Metric.isOpen_ball.inter (productSheetCarrier s).carrier_isClosed.isOpen_compl,
      ⟨Metric.mem_ball_self hδ, hx⟩, ?_⟩
    intro f _ hsupport
    have hbound : ∀ y : ℝ, f y ≠ 0 → |y - x| ≤ δ := by
      intro y hy
      have hball := (hsupport (subset_tsupport f hy)).1
      exact (by simpa only [Metric.mem_ball, Real.dist_eq] using hball : |y - x| < δ).le
    have hphys : productPhysicalDistribution s r f = 0 := by
      apply productPhysicalDistribution_atomicOnCarrier s r f
      intro y hy
      by_contra hnot
      exact (hsupport (subset_tsupport f hnot)).2 hy
    change (𝓕⁻ (productSpectralDistribution s r)) f - productPhysicalDistribution s r f = 0
    rw [hlocal f hbound, hphys, sub_self]

/-- Actual compatibility on ALL compact Schwartz tests, via an actual finite
smooth partition of their complete support. -/
theorem productFourierDefect_compact_zero (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) :
    productFourierDefect s r f = 0 :=
  Adaptive.distribution_eq_zero_of_local_vanishing _ f hf
    (fun x _ => productFourierDefect_locally_vanishes s r x)

/-- The ACTUAL inverse spectral record equals the ACTUAL original physical
record as a whole tempered distribution, with all analytic steps discharged. -/
theorem productSpectral_fourierInv_eq_physical (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    𝓕⁻ (productSpectralDistribution s r) = productPhysicalDistribution s r := by
  have hz : productFourierDefect s r = 0 := by
    ext f
    have hlim := ((productFourierDefect s r).continuous.tendsto f).comp
      (compactSchwartzApproximation_tendsto f)
    have hzero : ∀ N : ℕ, productFourierDefect s r (compactSchwartzApproximation N f) = 0 :=
      fun N => productFourierDefect_compact_zero s r _ (compactSchwartzApproximation_hasCompactSupport N f)
    have hzeroLim : Tendsto
        (fun N : ℕ => productFourierDefect s r (compactSchwartzApproximation N f))
        atTop (𝓝 0) := by
      simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique hlim hzeroLim
  exact sub_eq_zero.mp hz

/-- The exact original Fourier pair identity for EVERY complete original slab. -/
theorem productPhysical_fourier_eq_spectral (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    𝓕 (productPhysicalDistribution s r) = productSpectralDistribution s r := by
  rw [← productSpectral_fourierInv_eq_physical, FourierTransform.fourier_fourierInv_eq]

end

end MeyerGeneralProblem.StrongParity
