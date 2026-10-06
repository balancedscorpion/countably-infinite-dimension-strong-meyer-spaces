module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalCommonCarrier
public import MeyerGeneralProblem.Distribution.DisjointAtomicIndependence

@[expose] public section

/-!
# Actual infinite independent strongly tempered common-carrier sources

The common carrier contains a nonzero independent source from EVERY scheduled
private block. The lower Hamel rank is at least aleph_0. No countable upper
rank or finite-dimensional common exponent layer is asserted here.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- ALL distinct complete physical blocks are disjoint, as proved by actual cross-block root injectivity. -/
theorem originalScheduledFullPhysicalCarrier_pairwise_disjoint (bound : ℕ → ℕ) :
    Pairwise fun n m => Disjoint (originalScheduledFullPhysicalCarrier bound n).carrier
      (originalScheduledFullPhysicalCarrier bound m).carrier := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro x hxn hxm
  obtain ⟨i, k, he⟩ := (originalScheduledFullPhysicalCarrier_iff_label bound n x).mp hxn
  obtain ⟨j, l, hf⟩ := (originalScheduledFullPhysicalCarrier_iff_label bound m x).mp hxm
  have hh := originalScheduledPhysicalRoot_injective bound (he.trans hf.symm)
  exact hnm (congrArg (fun z : OriginalScheduledSheetLabel bound × ℤ => z.1.1) hh)

/-- ALL distinct actual private physical carriers, including every extra allowed point, are disjoint. -/
theorem originalScheduledPrivatePhysicalCarrier_pairwise_disjoint (bound : ℕ → ℕ) :
    Pairwise fun n m => Disjoint (originalScheduledPrivatePhysicalCarrier bound n).carrier
      (originalScheduledPrivatePhysicalCarrier bound m).carrier := by
  intro n m hnm
  exact (originalScheduledFullPhysicalCarrier_pairwise_disjoint bound hnm).mono
    (originalScheduledPrivatePhysicalCarrier_subset_full bound n)
    (originalScheduledPrivatePhysicalCarrier_subset_full bound m)

/-- The actual nonzero common-carrier source from EVERY block forms an infinite independent family. -/
theorem originalScheduledCommonSources_linearIndependent (bound : ℕ → ℕ) :
    LinearIndependent ℂ (fun n => originalScheduledPrivateLineSource (originalCommonWindowBounds bound) n) :=
  locallyAtomic_linearIndependent_of_disjoint (originalScheduledCommonCarrier bound)
    (fun n => originalScheduledPrivatePhysicalCarrier (originalCommonWindowBounds bound) n)
    (fun n => originalScheduledPrivateLineSource (originalCommonWindowBounds bound) n)
    (originalScheduledPrivatePhysicalCarrier_subset_common bound)
    (fun n => (originalScheduledPrivateLineSource_both_strong (originalCommonWindowBounds bound) n).1.1)
    (originalScheduledPrivateLineSource_ne_zero (originalCommonWindowBounds bound))
    (originalScheduledPrivatePhysicalCarrier_pairwise_disjoint (originalCommonWindowBounds bound))

/-- The COMPLETE original strong Meyer space of the actual common carrier has at least countable Hamel rank. -/
theorem originalScheduledCommonStrongSpace_aleph0_le_rank (bound : ℕ → ℕ) :
    Cardinal.aleph0 ≤ Module.rank ℂ (StronglyTemperedMeyerSpace (originalScheduledCommonCarrier bound)) := by
  let v : ℕ → StronglyTemperedMeyerSpace (originalScheduledCommonCarrier bound) :=
    fun n => ⟨originalScheduledPrivateLineSource (originalCommonWindowBounds bound) n,
      originalScheduledCommonSource_mem bound n⟩
  have hv : LinearIndependent ℂ v := by
    apply LinearIndependent.of_comp (f := (StronglyTemperedMeyerSpace (originalScheduledCommonCarrier bound)).subtype)
    exact originalScheduledCommonSources_linearIndependent bound
  exact hv.aleph0_le_rank

end

end MeyerGeneralProblem.StrongParity
