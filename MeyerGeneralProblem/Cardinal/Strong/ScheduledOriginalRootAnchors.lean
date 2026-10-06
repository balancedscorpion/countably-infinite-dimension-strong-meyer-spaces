module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixFixedExponents
public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalIndependentSources
public import MeyerGeneralProblem.Distribution.ReflectionSupportRecovery

@[expose] public section

/-! Actual nonzero private-root anchors and normalized full Schwartz tests.
The tests are constructed from the original sources and the ACTUAL finite
mixed prefix. All four native/reflected evaluation identities are derived
from original atomic action, root disjointness and cone symmetry. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- Every actual private spectral carrier in the prefix is included in its mixed carrier. -/
theorem originalScheduledPrivateSpectralCarrier_subset_prefix (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    (originalScheduledPrivateSpectralCarrier bound i.val).carrier ⊆
      (originalScheduledPrefixCarrier bound k).carrier :=
  fun _ hx => Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inr hx⟩)

/-- An actual original private root with nonzero mass; existence is proved from the source. -/
def originalScheduledRootAnchor (bound : ℕ → ℕ) (i : ℕ) :
    (originalScheduledPrivatePhysicalCarrier bound i).subtype :=
  Classical.choose (locallyAtomic_exists_isolationAction_ne_zero _ _
    (originalScheduledPrivateLineSource_both_strong bound i).1.1
    (originalScheduledPrivateLineSource_ne_zero bound i))

/-- The coefficient used to normalize the actual anchor test is nonzero internally. -/
theorem originalScheduledRootAnchor_coefficient_ne_zero (bound : ℕ → ℕ) (i : ℕ) :
    originalScheduledPrivateLineSource bound i
      ((originalScheduledPrivatePhysicalCarrier bound i).isolationSchwartz
        (originalScheduledRootAnchor bound i)) ≠ 0 :=
  Classical.choose_spec (locallyAtomic_exists_isolationAction_ne_zero _ _
    (originalScheduledPrivateLineSource_both_strong bound i).1.1
    (originalScheduledPrivateLineSource_ne_zero bound i))

/-- The SAME actual root point in the complete mixed finite prefix. -/
def originalScheduledPrefixAnchorPoint (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    (originalScheduledPrefixCarrier bound k).subtype :=
  LocallyFiniteCarrier.inclusion (originalScheduledPrivatePhysicalCarrier_subset_prefix bound k i)
    (originalScheduledRootAnchor bound i.val)

/-- The actual prefix isolator, normalized by the internally nonzero original mass. -/
def originalScheduledPrefixAnchorTest (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) : SchwartzMap ℝ ℂ :=
  (originalScheduledPrivateLineSource bound i.val
    ((originalScheduledPrivatePhysicalCarrier bound i.val).isolationSchwartz
      (originalScheduledRootAnchor bound i.val)))⁻¹ •
        (originalScheduledPrefixCarrier bound k).isolationSchwartz
          (originalScheduledPrefixAnchorPoint bound k i)

/-- Each normalized anchor test has actual compact support. -/
theorem originalScheduledPrefixAnchorTest_hasCompactSupport (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    HasCompactSupport (originalScheduledPrefixAnchorTest bound k i : ℝ → ℂ) := by
  exact ((originalScheduledPrefixCarrier bound k).isolationSchwartz_hasCompactSupport
    (originalScheduledPrefixAnchorPoint bound k i)).smul_left

/-- Actual normalized native observations are the Kronecker matrix, including ALL deleted rows. -/
theorem originalScheduledPrefixAnchorTest_native (bound : ℕ → ℕ) (k : ℕ) (i j : Fin k) :
    originalScheduledPrivateLineSource bound j.val (originalScheduledPrefixAnchorTest bound k i) =
      if j = i then 1 else 0 := by
  classical
  unfold originalScheduledPrefixAnchorTest
  rw [map_smul, smul_eq_mul]
  by_cases hji : j = i
  · subst j
    rw [originalScheduledPrefixAnchorPoint, isolationAction_eq_of_carrier_subset _ _
      (originalScheduledPrivateLineSource_both_strong bound i.val).1.1]
    simp [originalScheduledRootAnchor_coefficient_ne_zero]
  · have hz : originalScheduledPrivateLineSource bound j.val
        ((originalScheduledPrefixCarrier bound k).isolationSchwartz
          (originalScheduledPrefixAnchorPoint bound k i)) = 0 := by
      apply locallyAtomic_isolationAction_eq_zero_of_not_mem
        (originalScheduledPrefixCarrier bound k)
        (fun j : Fin k => originalScheduledPrivatePhysicalCarrier bound j.val)
        (fun j : Fin k => originalScheduledPrivateLineSource bound j.val)
        (originalScheduledPrivatePhysicalCarrier_subset_prefix bound k)
        (fun j => (originalScheduledPrivateLineSource_both_strong bound j.val).1.1) j
      intro hx
      exact Set.disjoint_left.mp
        (originalScheduledPrivatePhysicalCarrier_pairwise_disjoint bound
          (fun he => hji (Fin.ext he))) hx (originalScheduledRootAnchor bound i.val).property
    simp [hz, hji]

/-- Every actual root anchor avoids ALL original spectral carriers in its prefix. -/
theorem originalScheduledPrefixAnchorPoint_not_spectral (bound : ℕ → ℕ) (k : ℕ) (i j : Fin k) :
    (originalScheduledPrefixAnchorPoint bound k i : ℝ) ∉
      (originalScheduledPrivateSpectralCarrier bound j.val).carrier := by
  intro hx
  apply Set.disjoint_left.mp (originalScheduledPrefixFullRoots_disjoint_cone bound k)
    (originalScheduledFullPhysicalCarrier_subset_prefixRoots bound k i
      (originalScheduledPrivatePhysicalCarrier_subset_full bound i.val
        (originalScheduledRootAnchor bound i.val).property))
  exact originalScheduledPrivateSpectralCarrier_subset_prefixCone bound k j hx

/-- The FULL normalized Schwartz test vanishes on EVERY original spectral carrier in the prefix. -/
theorem originalScheduledPrefixAnchorTest_vanishes_spectral (bound : ℕ → ℕ) (k : ℕ) (i j : Fin k) :
    SchwartzVanishesOn (originalScheduledPrivateSpectralCarrier bound j.val)
      (originalScheduledPrefixAnchorTest bound k i) := by
  intro x hx
  change _ * (originalScheduledPrefixCarrier bound k).isolationSchwartz
    (originalScheduledPrefixAnchorPoint bound k i) x = 0
  rw [(originalScheduledPrefixCarrier bound k).isolationSchwartz_of_mem_of_ne _
    (originalScheduledPrivateSpectralCarrier_subset_prefix bound k j hx)
    (fun he => originalScheduledPrefixAnchorPoint_not_spectral bound k i j (he ▸ hx)), mul_zero]

/-- Every genuine native Fourier record annihilates all actual root anchor tests. -/
theorem originalScheduledPrefixAnchorTest_native_fourier (bound : ℕ → ℕ) (k : ℕ) (i j : Fin k) :
    𝓕 (originalScheduledPrivateLineSource bound j.val) (originalScheduledPrefixAnchorTest bound k i) = 0 :=
  hasLocallyAtomicAction_atomicOnCarrier _ _
    (originalScheduledPrivateLineSource_both_strong bound j.val).2.1 _
    (originalScheduledPrefixAnchorTest_vanishes_spectral bound k i j)

/-- The genuine inverse Fourier mode is atomic on its SAME allowed symmetric cone carrier. -/
theorem originalScheduledPrivateLineSource_inverse_atomic (bound : ℕ → ℕ) (i : ℕ) :
    AtomicOnCarrier (originalScheduledPrivateSpectralCarrier bound i)
      (𝓕⁻ (originalScheduledPrivateLineSource bound i)) := by
  apply atomicOnCarrier_of_originalDistributionReflection _
    (fun x hx => (originalScheduledPrivateSpectralCarrier_neg_iff bound i x).mpr hx)
  rw [← fourier_fourier_eq_originalDistributionReflection, FourierTransform.fourier_fourierInv_eq]
  exact hasLocallyAtomicAction_atomicOnCarrier _ _
    (originalScheduledPrivateLineSource_both_strong bound i).2.1

/-- Every actual inverse Fourier mode annihilates all physical root anchor tests. -/
theorem originalScheduledPrefixAnchorTest_inverse (bound : ℕ → ℕ) (k : ℕ) (i j : Fin k) :
    𝓕⁻ (originalScheduledPrivateLineSource bound j.val) (originalScheduledPrefixAnchorTest bound k i) = 0 :=
  originalScheduledPrivateLineSource_inverse_atomic bound j.val _
    (originalScheduledPrefixAnchorTest_vanishes_spectral bound k i j)

/-- The genuine spectral record of an inverse mode has the exact normalized Kronecker observation. -/
theorem originalScheduledPrefixAnchorTest_inverse_fourier (bound : ℕ → ℕ) (k : ℕ) (i j : Fin k) :
    𝓕 (𝓕⁻ (originalScheduledPrivateLineSource bound j.val)) (originalScheduledPrefixAnchorTest bound k i) =
      if j = i then 1 else 0 := by
  rw [FourierTransform.fourier_fourierInv_eq, originalScheduledPrefixAnchorTest_native]

end
end MeyerGeneralProblem.StrongParity
