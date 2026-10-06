module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalSparseGeometry

@[expose] public section

/-! Every original common-module array has the literal sparse private support.
The shared coarse points survive. Empty-prefix strong arrays are truly zero by
the actual unit annihilator, rather than excluded by a nonempty-prefix premise. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The actual union of BOTH-coordinate private integer sublattices at the common scale. -/
def originalScheduledPrefixSparseLabels (bound : ℕ → ℕ) (k : ℕ) : Set (ℤ × ℤ) :=
  ⋃ i : Fin k, Set.range (originalIntegerCoordinateDilation (originalScheduledPrefixCoordinateDilation bound k i))

/-- Any common-module carrier point in a nonempty prefix belongs to a LITERAL
allowed private spectral carrier; no physical root contributes such a row. -/
theorem originalScheduledPrefixModulePoint_mem_private_spectral (bound : ℕ → ℕ) (k : ℕ)
    (hk : 0 < k) (z : ℤ × ℤ)
    (hz : originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z ∈
      (originalScheduledPrefixCarrier bound k).carrier) :
    ∃ i : Fin k, originalScaledModuleFrequencyHom
      (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z ∈
        (originalScheduledPrivateSpectralCarrier bound i.val).carrier := by
  rcases hz with hc | hp
  · exact ⟨⟨0, hk⟩, originalScheduledPrivateSpectralCarrier_coarse bound 0 hc⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    rcases hi with hphys | hspec
    · apply False.elim
      apply originalScheduledPrefixRootSet_not_mem_module bound k _
        (Set.mem_iUnion.mpr ⟨i, originalScheduledPrivatePhysicalCarrier_subset_full bound i.val hphys⟩)
      exact originalScaledModuleFrequency_mem_rational_module _ (originalScheduledPrefixDenominator_pos bound k) z
    · exact ⟨i, hspec⟩

/-- The whole common-module carrier has the true sparse private coordinate support. -/
theorem originalScheduledPrefixModulePoint_sparse_labels (bound : ℕ → ℕ) (k : ℕ) (hk : 0 < k)
    (z : ℤ × ℤ)
    (hz : originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z ∈
      (originalScheduledPrefixCarrier bound k).carrier) : z ∈ originalScheduledPrefixSparseLabels bound k := by
  obtain ⟨i, hi⟩ := originalScheduledPrefixModulePoint_mem_private_spectral bound k hk z hz
  exact Set.mem_iUnion.mpr ⟨i, originalScheduledPrivateSpectral_common_label bound k i z hi⟩

/-- The ACTUAL empty-prefix Laurent polynomial is exactly the unit coefficient at zero. -/
theorem originalScheduledPrefixIntegerCoefficients_zero (bound : ℕ → ℕ) :
    originalScheduledPrefixIntegerCoefficients bound 0 = Finsupp.single (0, 0) 1 := by
  change Finsupp.mapDomain originalNativeIntegerEmbedding (Finsupp.single (0, 0) (1 : ℂ)) = _
  rw [Finsupp.mapDomain_single]
  rfl

/-- Every original strong EMPTY-prefix module row is zero by its GENUINE unit recurrence. -/
theorem originalScheduledPrefixFourierArray_empty (bound : ℕ → ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound 0)) (z : ℤ × ℤ) :
    originalScheduledPrefixFourierArray bound 0 T z = 0 := by
  have h := originalScheduledPrefixIntegerArray_annihilated bound 0 T hT z
  rw [originalScheduledPrefixIntegerCoefficients_zero] at h
  simpa [annihilatorArrayConvolution, show (0, 0) = (0 : ℤ × ℤ) from rfl] using h

/-- EVERY complete ORIGINAL strong pair has the full literal sparse array on ALL
integer labels, with the empty case, both signs, axes and origin supplied internally. -/
theorem originalScheduledPrefixFourierArray_zero_off_sparse (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (z : ℤ × ℤ) (hz : z ∉ originalScheduledPrefixSparseLabels bound k) :
    originalScheduledPrefixFourierArray bound k T z = 0 := by
  classical
  by_cases hk : k = 0
  · subst k
    exact originalScheduledPrefixFourierArray_empty bound T hT z
  · have hnot : originalScaledModuleFrequencyHom
        (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z ∉
          (originalScheduledPrefixCarrier bound k).carrier :=
      fun hc => hz (originalScheduledPrefixModulePoint_sparse_labels bound k (Nat.pos_of_ne_zero hk) z hc)
    unfold originalScheduledPrefixFourierArray extendedAtomicCoefficient
    exact dite_eq_right hnot

end
end MeyerGeneralProblem.StrongParity
