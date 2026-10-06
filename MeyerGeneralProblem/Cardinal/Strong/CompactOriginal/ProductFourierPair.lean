module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.LocalProductJump
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.PhysicalDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductResidues
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductFourierPair
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.NonPoleProductJump

@[expose] public section

/-! Original ProductFourierPair for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open Filter Set
open scoped Topology FourierTransform

/-- The literal difference between the actual inverse spectral record and
the actual original physical record. -/
def productFourierDefect {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    TemperedDistribution ℝ ℂ :=
  𝓕⁻ (productSpectralDistribution block r) - productPhysicalDistribution block r

/-- The complete original Fourier defect vanishes on a genuine open
neighborhood of EVERY real point, including every original pole. -/
theorem productFourierDefect_locally_vanishes {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : ℝ) : ∃ O : Set ℝ, IsOpen O ∧ x ∈ O ∧
      Adaptive.DistributionVanishesOn O (productFourierDefect block r) := by
  classical
  by_cases hx : x ∈ (compactOriginalProductSheetCarrier block).carrier
  · let a : (compactOriginalProductSheetCarrier block).subtype := ⟨x, hx⟩
    obtain ⟨δ, hδ, hlocal⟩ := productSpectral_fourierInv_local_root block r a
    let O : Set ℝ := Metric.ball x δ ∩
      Metric.ball x ((compactOriginalProductSheetCarrier block).isolationRadius a)
    refine ⟨O, Metric.isOpen_ball.inter Metric.isOpen_ball,
      ⟨Metric.mem_ball_self hδ, Metric.mem_ball_self
        ((compactOriginalProductSheetCarrier block).isolationRadius_pos a)⟩, ?_⟩
    intro f _ hsupport
    have hbound : ∀ y : ℝ, f y ≠ 0 → |y - (a : ℝ)| ≤ δ := by
      intro y hy
      have hball := (hsupport (subset_tsupport f hy)).1
      exact (by simpa only [Metric.mem_ball, Real.dist_eq] using hball : |y - x| < δ).le
    have hphys : productPhysicalDistribution block r f = productPhysicalResidue block r a * f a := by
      rw [productPhysicalDistribution_apply, tsum_eq_single a]
      intro b hb
      have hb0 : f b = 0 := by
        by_contra hnot
        have hball := (hsupport (subset_tsupport f hnot)).2
        have hdist : dist (b : ℝ) (a : ℝ) <
            (compactOriginalProductSheetCarrier block).isolationRadius a := hball
        have hsep := (compactOriginalProductSheetCarrier block).isolationRadius_le_dist a b.property
          (fun h => hb (Subtype.ext h))
        exact (not_lt_of_ge hsep) hdist
      rw [hb0, mul_zero]
    change (𝓕⁻ (productSpectralDistribution block r)) f - productPhysicalDistribution block r f = 0
    rw [hlocal f hbound, hphys, sub_self]
  · obtain ⟨δ, hδ, hlocal⟩ := productSpectral_fourierInv_local_nonpole block r x hx
    let O : Set ℝ := Metric.ball x δ ∩ (compactOriginalProductSheetCarrier block).carrierᶜ
    refine ⟨O, Metric.isOpen_ball.inter (compactOriginalProductSheetCarrier block).carrier_isClosed.isOpen_compl,
      ⟨Metric.mem_ball_self hδ, hx⟩, ?_⟩
    intro f _ hsupport
    have hbound : ∀ y : ℝ, f y ≠ 0 → |y - x| ≤ δ := by
      intro y hy
      have hball := (hsupport (subset_tsupport f hy)).1
      exact (by simpa only [Metric.mem_ball, Real.dist_eq] using hball : |y - x| < δ).le
    have hphys : productPhysicalDistribution block r f = 0 := by
      apply productPhysicalDistribution_atomicOnCarrier block r f
      intro y hy
      by_contra hnot
      exact (hsupport (subset_tsupport f hnot)).2 hy
    change (𝓕⁻ (productSpectralDistribution block r)) f - productPhysicalDistribution block r f = 0
    rw [hlocal f hbound, hphys, sub_self]

/-- Actual compatibility on ALL compact Schwartz tests, via an actual finite
smooth partition of their complete support. -/
theorem productFourierDefect_compact_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) :
    productFourierDefect block r f = 0 :=
  Adaptive.distribution_eq_zero_of_local_vanishing _ f hf
    (fun x _ => productFourierDefect_locally_vanishes block r x)

/-- The ACTUAL inverse spectral record equals the ACTUAL original physical
record as a whole tempered distribution, with all analytic steps discharged. -/
theorem productSpectral_fourierInv_eq_physical {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    𝓕⁻ (productSpectralDistribution block r) = productPhysicalDistribution block r := by
  have hz : productFourierDefect block r = 0 := by
    ext f
    have hlim := ((productFourierDefect block r).continuous.tendsto f).comp
      (compactSchwartzApproximation_tendsto f)
    have hzero : ∀ N : ℕ, productFourierDefect block r (compactSchwartzApproximation N f) = 0 :=
      fun N => productFourierDefect_compact_zero block r _ (compactSchwartzApproximation_hasCompactSupport N f)
    have hzeroLim : Tendsto
        (fun N : ℕ => productFourierDefect block r (compactSchwartzApproximation N f))
        atTop (𝓝 0) := by
      simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique hlim hzeroLim
  exact sub_eq_zero.mp hz

/-- The exact original Fourier pair identity for EVERY complete original slab. -/
theorem productPhysical_fourier_eq_spectral {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    𝓕 (productPhysicalDistribution block r) = productSpectralDistribution block r := by
  rw [← productSpectral_fourierInv_eq_physical, FourierTransform.fourier_fourierInv_eq]

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
