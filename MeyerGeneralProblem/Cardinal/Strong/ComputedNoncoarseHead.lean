module

public import MeyerGeneralProblem.Cardinal.Strong.ComputedSignedHeadLabels
public import MeyerGeneralProblem.Cardinal.Strong.PrivateScaledSpectralCone

@[expose] public section

/-! The actual noncoarse original head mask, computed internally from the
complete signed head and BOTH private-coordinate divisibility tests. -/

namespace MeyerGeneralProblem.StrongParity

/-- Ordinary exact shared-coarse test of both coordinates of either original sign. -/
def originalSpectralCoarseTest (m : ℕ) (label : spectralConeIndex) : Bool :=
  decide (m ∣ (spectralConeIndexCoordinates label).1 ∧ m ∣ (spectralConeIndexCoordinates label).2)

/-- Implemented complete noncoarse head enumeration; zero is retained by the coarse cone. -/
def computedOriginalNoncoarseHeadLabels (s m : ℕ) : Finset spectralConeIndex :=
  (computedOriginalSignedHeadLabels s).filter (fun p => originalSpectralCoarseTest m p = false)

noncomputable section

/-- The computed coarse decision is exactly geometric membership in the ACTUAL shared cone. -/
theorem originalSpectralCoarseTest_iff (m : ℕ) (hm : 0 < m) (label : spectralConeIndex) :
    originalSpectralCoarseTest m label = true ↔
      originalPrivateSpectralLabelValue m label ∈ originalSharedCoarseCone.carrier := by
  rw [originalPrivateSpectralLabelValue_coarse_divisibility m hm label]
  simp only [originalSpectralCoarseTest, decide_eq_true_eq]

/-- Every computed noncoarse head label satisfies the literal original complete mask, and conversely. -/
theorem mem_computedOriginalNoncoarseHeadLabels_iff (s m : ℕ) (label : spectralConeIndex) :
    label ∈ computedOriginalNoncoarseHeadLabels s m ↔
      |spectralConeIndexFrequency label| ≤ ((s / 2 : ℕ) : ℝ) / 2 ∧
        ¬(m ∣ (spectralConeIndexCoordinates label).1 ∧ m ∣ (spectralConeIndexCoordinates label).2) := by
  rw [computedOriginalNoncoarseHeadLabels, Finset.mem_filter, mem_computedOriginalSignedHeadLabels_iff]
  simp only [originalSpectralCoarseTest, decide_eq_false_iff_not]

/-- The output is precisely the forbidden private spectral head outside the ACTUAL shared coarse cone. -/
theorem mem_computedOriginalNoncoarseHeadLabels_geometric (s m : ℕ) (hm : 0 < m)
    (label : spectralConeIndex) :
    label ∈ computedOriginalNoncoarseHeadLabels s m ↔
      |originalPrivateSpectralLabelValue m label| ≤
        (((s / 2 : ℕ) : ℝ) / 2) / (parityDilationUnit * (m : ℝ)) ∧
        originalPrivateSpectralLabelValue m label ∉ originalSharedCoarseCone.carrier := by
  rw [mem_computedOriginalNoncoarseHeadLabels_iff,
    originalPrivateSpectralLabelValue_head_iff s m hm,
    originalPrivateSpectralLabelValue_coarse_divisibility m hm]

/-- Zero is never deleted by the implemented noncoarse head mask. -/
theorem zero_not_mem_computedOriginalNoncoarseHeadLabels (s m : ℕ) :
    originalUpperSpectralLabel (0, 0) ∉ computedOriginalNoncoarseHeadLabels s m := by
  rw [mem_computedOriginalNoncoarseHeadLabels_iff]
  simp [originalUpperSpectralLabel, spectralConeIndexCoordinates]

/-- Unit private scale has no forbidden noncoarse head labels at ANY order. -/
theorem computedOriginalNoncoarseHeadLabels_one (s : ℕ) :
    computedOriginalNoncoarseHeadLabels s 1 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro label
  rw [mem_computedOriginalNoncoarseHeadLabels_iff]
  simp

end

end MeyerGeneralProblem.StrongParity
