module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrivateIntersections
public import MeyerGeneralProblem.Distribution.RestrictedAtomicRows

@[expose] public section

/-! Actual original forbidden rows of EACH genuine reconstructed native source.
Complete original membership supplies all physical deletions and noncoarse
Fourier head zeros internally. Every source consequently belongs to the actual
private strong pair and its actual one-dimensional source line. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- At EVERY noncoarse actual private-cone point, the full Fourier sum
isolates exactly that block's genuine original Fourier coefficient. -/
theorem originalScheduledNativeSource_sum_fourier_noncoarse_isolation (bound : ℕ → ℕ) (k : ℕ)
    (r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ)
    (i : Fin k)
    (x : (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i.val)
      (originalScheduledBlockPrime_pos bound i.val)).subtype)
    (hx : (x : ℝ) ∉ originalSharedCoarseCone.carrier) :
    (𝓕 (∑ j : Fin k, originalScheduledNativeSource bound j.val (r j)))
      ((originalScheduledPrefixCone bound k).isolationSchwartz
        ⟨x, originalScheduledFullPrivateCone_subset_prefixCone bound k i x.property⟩) =
    (𝓕 (originalScheduledNativeSource bound i.val (r i)))
      ((originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i.val)
        (originalScheduledBlockPrime_pos bound i.val)).isolationSchwartz x) := by
  classical
  change (temperedFourierLinearMap (∑ j : Fin k, originalScheduledNativeSource bound j.val (r j))) _ = _
  rw [map_sum, _root_.sum_apply]
  simp only [temperedFourierLinearMap_apply]
  rw [Finset.sum_eq_single i]
  · exact isolationAction_eq_of_carrier_subset
      (originalScheduledFullPrivateCone_subset_prefixCone bound k i) _
      (atomicOnCarrier_hasLocallyAtomicAction _ _
        (originalScheduledNativeSource_fourier_atomicOnPrivateCone bound i.val (r i))) x
  · intro j _ hji
    rw [atomic_isolation_apply_on_larger_carrier _ _
      (originalScheduledFullPrivateCone_subset_prefixCone bound k j) _
      (originalScheduledNativeSource_fourier_atomicOnPrivateCone bound j.val (r j))]
    apply dite_eq_right
    intro hj
    apply hx
    rw [← originalScheduledFullPrivateCones_inter bound i.val j.val
      (fun he => hji (Fin.ext he).symm)]
    exact ⟨x.property, hj⟩
  · simp

/-- EVERY actual original pair internally reconstructs full native sources
with ALL original physical deletion and Fourier noncoarse-head equations. -/
theorem originalScheduledPrefixRootSource_native_sum_private_rows (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    ∃ r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ,
      originalScheduledPrefixRootSource bound k N T hF =
        ∑ i : Fin k, originalScheduledNativeSource bound i.val (r i) ∧
      (∀ (i : Fin k) (x : (originalScheduledFullPhysicalCarrier bound i.val).subtype),
        (x : ℝ) ∉ (originalScheduledPrivatePhysicalCarrier bound i.val).carrier →
        originalScheduledNativeSource bound i.val (r i)
          ((originalScheduledFullPhysicalCarrier bound i.val).isolationSchwartz x) = 0) ∧
      (∀ (i : Fin k)
        (x : (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i.val)
          (originalScheduledBlockPrime_pos bound i.val)).subtype),
        (x : ℝ) ∈ originalPrivateGeometricHead (originalReflectedOrderSchedule bound i.val)
          (originalReflectedPrimeSchedule bound i.val) →
        (𝓕 (originalScheduledNativeSource bound i.val (r i)))
          ((originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i.val)
            (originalScheduledBlockPrime_pos bound i.val)).isolationSchwartz x) = 0) := by
  obtain ⟨r, hr, hz⟩ := originalScheduledPrefixRootSource_native_sum_deleted_roots bound k M N T hT hF
  refine ⟨r, hr, ?_, ?_⟩
  · intro i x hx
    exact hz i x (fun hp => hx
      ((originalScheduledFullPhysicalCarrier_prefix_iff bound k i x x.property).mp hp))
  · intro i x hx
    rw [← originalScheduledNativeSource_sum_fourier_noncoarse_isolation bound k r i x hx.2, ← hr]
    exact atomic_isolation_eq_zero_off_other_carrier _ _ _
      (originalScheduledPrefixRootSource_fourier_atomicOnCone bound k N T hF)
      (hasLocallyAtomicAction_atomicOnCarrier _ _
        (originalScheduledPrefixRootSource_both_original_strong bound k M N T hT hF).2.1)
      _ (originalScheduledPrivateHead_not_mem_prefix bound k i x x.property hx)

/-- Literal physical and Fourier rows on the ACTUAL full source force
BOTH records onto the ACTUAL private supports at their proved source exponents. -/
theorem originalScheduledNativeSource_both_private_strong_of_rows (bound : ℕ → ℕ) (i : ℕ)
    (r : productNumeratorIndex (originalReflectedOrderSchedule bound i) → ℂ)
    (hphysical : ∀ x : (originalScheduledFullPhysicalCarrier bound i).subtype,
      (x : ℝ) ∉ (originalScheduledPrivatePhysicalCarrier bound i).carrier →
      originalScheduledNativeSource bound i r
        ((originalScheduledFullPhysicalCarrier bound i).isolationSchwartz x) = 0)
    (hspectral : ∀ x : (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i)
      (originalScheduledBlockPrime_pos bound i)).subtype,
      (x : ℝ) ∈ originalPrivateGeometricHead (originalReflectedOrderSchedule bound i)
        (originalReflectedPrimeSchedule bound i) →
      (𝓕 (originalScheduledNativeSource bound i r))
        ((originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i)
          (originalScheduledBlockPrime_pos bound i)).isolationSchwartz x) = 0) :
    originalScheduledNativeSource bound i r ∈ stronglyTemperedAtomicAtExponent
      (originalScheduledPrivatePhysicalCarrier bound i) ((originalReflectedOrderSchedule bound i - 1) + 2) ∧
    𝓕 (originalScheduledNativeSource bound i r) ∈ stronglyTemperedAtomicAtExponent
      (originalScheduledPrivateSpectralCarrier bound i) (originalReflectedOrderSchedule bound i + 3) := by
  have hfull := originalScheduledNativeSource_both_strong bound i r
  constructor
  · apply stronglyTemperedAtomicAtExponent_delete
    · apply (atomicOnCarrier_delete_iff _ _ _).mpr
      refine ⟨originalScheduledNativeSource_atomicOnRoots bound i r, ?_⟩
      intro x hx
      exact hphysical x (fun hp => hp.2 hx)
    · exact hfull.1
  · exact stronglyTemperedAtomicAtExponent_delete _ _ _ _
      ((atomicOnCarrier_delete_iff _ _ _).mpr
        ⟨originalScheduledNativeSource_fourier_atomicOnPrivateCone bound i r, hspectral⟩) hfull.2

/-- EVERY complete original prefix pair's genuine root source is a sum of
ACTUAL scheduled private lines. All original deleted rows, private support and
BOTH strong records of each native source are derived internally. -/
theorem originalScheduledPrefixRootSource_native_private_lines (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    ∃ r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ,
    ∃ a : Fin k → ℂ,
      originalScheduledPrefixRootSource bound k N T hF =
        ∑ i : Fin k, a i • originalScheduledPrivateLineSource bound i.val ∧
      (∀ i : Fin k, originalScheduledNativeSource bound i.val (r i) =
        a i • originalScheduledPrivateLineSource bound i.val) ∧
      (∀ i : Fin k, originalScheduledNativeSource bound i.val (r i) ∈
        originalScheduledPrivateStrongPair bound i.val) := by
  classical
  obtain ⟨r, hr, hp, hs⟩ := originalScheduledPrefixRootSource_native_sum_private_rows bound k M N T hT hF
  have hmem : ∀ i : Fin k, originalScheduledNativeSource bound i.val (r i) ∈
      originalScheduledPrivateStrongPair bound i.val := by
    intro i
    have h := originalScheduledNativeSource_both_private_strong_of_rows bound i.val (r i) (hp i) (hs i)
    change originalScheduledNativeSource bound i.val (r i) ∈
      StronglyTemperedAtomicOnCarrier (originalScheduledPrivatePhysicalCarrier bound i.val) ∧
      𝓕 (originalScheduledNativeSource bound i.val (r i)) ∈
        StronglyTemperedAtomicOnCarrier (originalScheduledPrivateSpectralCarrier bound i.val)
    exact ⟨(mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
        ⟨(originalReflectedOrderSchedule bound i.val - 1) + 2, h.1⟩,
      (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
        ⟨originalReflectedOrderSchedule bound i.val + 3, h.2⟩⟩
  have hlines : ∀ i : Fin k, ∃ a : ℂ, originalScheduledNativeSource bound i.val (r i) =
      a • originalScheduledPrivateLineSource bound i.val := by
    intro i
    exact (originalScheduledPrivateStrongPair_complete_span bound i.val
      (originalScheduledNativeSource bound i.val (r i))).mp (hmem i)
  choose a ha using hlines
  refine ⟨r, a, ?_, ha, hmem⟩
  rw [hr]
  exact Finset.sum_congr rfl fun i _ => ha i

/-- COMPLETE original strong membership ALONE gives the private-line root
sum and genuine cone/root companion, with BOTH SAME original M,N records. -/
theorem originalScheduledPrefix_complete_private_line_root_decomposition (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ a : Fin k → ℂ, ∃ M N : ℕ,
      let ρ := ∑ i : Fin k, a i • originalScheduledPrivateLineSource bound i.val
      AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k) ρ ∧
      AtomicOnCarrier (originalScheduledPrefixCone bound k) (𝓕 ρ) ∧
      AtomicOnCarrier (originalScheduledPrefixCone bound k) (T - ρ) ∧
      AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k) (𝓕 (T - ρ)) ∧
      ρ ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M ∧
      𝓕 ρ ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N ∧
      T - ρ ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M ∧
      𝓕 (T - ρ) ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N := by
  obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT.1
  obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hT.2
  have hM' : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M := hM
  have hN' : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N := hN
  obtain ⟨_, a, ha, _⟩ := originalScheduledPrefixRootSource_native_private_lines bound k M N T hM' hN'
  refine ⟨a, M, N, ?_⟩
  dsimp only
  rw [← ha]
  have hρ := originalScheduledPrefixRootSource_both_original_strong bound k M N T hM' hN'
  have hC := originalScheduledPrefixRootSource_complement_both_original_strong bound k M N T hM' hN'
  exact ⟨originalScheduledPrefixRootSource_atomicOnRoots bound k M N T hM' hN',
    originalScheduledPrefixRootSource_fourier_atomicOnCone bound k N T hN',
    originalScheduledPrefixRootSource_complement_atomicOnCone bound k M N T hM' hN',
    originalScheduledPrefixRootSource_complement_fourier_atomicOnRoots bound k N T hN',
    hρ.1, hρ.2, hC.1, hC.2⟩

end
end MeyerGeneralProblem.StrongParity
