module

public import MeyerGeneralProblem.Distribution.OriginalWindowC0Approximation

@[expose] public section

/-! Exact intersection of genuine prefix-plus-exterior dual constraints.
EVERY full C0 vanishing test is recovered using actual norm-convergent
cutoffs and the two genuine bounded record functionals. The resulting
intersection recovers BOTH WHOLE original SAME-N strong records internally. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty FourierTransform

/-- The explicit window radii increase strictly. -/
theorem originalWindowRadius_strictMono : StrictMono originalWindowRadius := by
  intro i j h
  have hj : (i : ℝ) < j := by exact_mod_cast h
  unfold originalWindowRadius
  linarith

/-- BOTH entire C0 support ideals at the intersection are EXACTLY the prefix ideals. -/
theorem originalWeightedDualSetConstraints_window_iInter (L : Set ℝ) :
    (⋂ n : ℕ, originalWeightedDualSetConstraints
      (originalExteriorWindow L (originalWindowRadius n))) = originalWeightedDualSetConstraints L := by
  ext q
  constructor
  · intro hq g hg
    have hz (n : ℕ) := (Set.mem_iInter.mp hq n) (originalWindowC0Cutoff n * g)
      (originalWindowC0Cutoff_mul_vanishes L n g hg)
    have hc := originalWindowC0Cutoff_mul_tendsto g
    constructor
    · have ht : Filter.Tendsto
          (fun n : ℕ => q (originalWindowC0Cutoff n * g, 0)) Filter.atTop (nhds (q (g, 0))) :=
        ((originalDualPhysicalC0Record q).continuous.tendsto g).comp hc
      have hzero : Filter.Tendsto
          (fun n : ℕ => q (originalWindowC0Cutoff n * g, 0)) Filter.atTop (nhds 0) := by
        convert tendsto_const_nhds using 1
        funext n
        exact (hz n).1
      exact tendsto_nhds_unique ht hzero
    · have ht : Filter.Tendsto
          (fun n : ℕ => q (0, originalWindowC0Cutoff n * g)) Filter.atTop (nhds (q (0, g))) :=
        ((originalDualSpectralC0Record q).continuous.tendsto g).comp hc
      have hzero : Filter.Tendsto
          (fun n : ℕ => q (0, originalWindowC0Cutoff n * g)) Filter.atTop (nhds 0) := by
        convert tendsto_const_nhds using 1
        funext n
        exact (hz n).2
      exact tendsto_nhds_unique ht hzero
  · intro hq
    apply Set.mem_iInter.mpr
    intro n
    exact originalWeightedDualSetConstraints_mono
      (originalExteriorWindow_contains L (originalWindowRadius n)) hq

/-- The actual nested compact window Fourier unit balls intersect EXACTLY
in the genuine original supported dual unit ball. -/
theorem originalWeightedDualWindowBall_iInter (S : LocallyFiniteCarrier) (N : ℕ) :
    (⋂ n : ℕ, originalWeightedDualWindowBall S N (originalWindowRadius n)) =
      originalWeightedDualSupportedFourierPairBall S N := by
  ext q
  constructor
  · intro hq
    refine ⟨(Set.mem_iInter.mp hq 0).1, ?_⟩
    rw [← originalWeightedDualSetConstraints_eq_carrier,
      ← originalWeightedDualSetConstraints_window_iInter]
    exact Set.mem_iInter.mpr (fun n => (Set.mem_iInter.mp hq n).2)
  · intro hq
    exact Set.mem_iInter.mpr (fun n =>
      originalWeightedDualSupportedFourierPairBall_subset_window S N (originalWindowRadius n) hq)

/-- Actual nested-window membership ALONE recovers BOTH WHOLE original
strong records at the SAME exponent with the SUM of their original variations <=1. -/
theorem originalWeightedDualWindowBall_iInter_original_strong
    (S : LocallyFiniteCarrier) (N : ℕ) (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)))
    (hq : ∀ n : ℕ, q ∈ originalWeightedDualWindowBall S N (originalWindowRadius n)) :
    originalWeightedDualPhysicalDistribution N q ∈ stronglyTemperedAtomicAtExponent S N ∧
      𝓕 (originalWeightedDualPhysicalDistribution N q) ∈ stronglyTemperedAtomicAtExponent S N ∧
      originalStrongPairVariation S N (originalWeightedDualPhysicalDistribution N q) ≤ 1 := by
  apply originalWeightedDualSupportedFourierPairBall_original_strong S N q
  rw [← originalWeightedDualWindowBall_iInter]
  exact Set.mem_iInter.mpr hq

/-- The physical image of the exact nested intersection is the COMPLETE
original SAME-N strong unit ball, including every original Fourier pair. -/
theorem originalStrongPairUnitBall_eq_window_intersection_image
    (S : LocallyFiniteCarrier) (N : ℕ) :
    originalStrongPairUnitBall S N = originalWeightedDualPhysicalDistribution N ''
      (⋂ n : ℕ, originalWeightedDualWindowBall S N (originalWindowRadius n)) := by
  rw [originalWeightedDualWindowBall_iInter, originalStrongPairUnitBall_eq_supported_dual_image]

end
end MeyerGeneralProblem
