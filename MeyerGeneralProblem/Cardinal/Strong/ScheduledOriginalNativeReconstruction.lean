module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalNativeSourceAlgebra
public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalIndependentSources

@[expose] public section

/-! WHOLE original finite-prefix native-source reconstruction. EVERY complete
original strong pair internally supplies its native slabs and its exact source
sum; actual physical deletions follow AFTER whole-distribution equality. The
cone/root companion and BOTH original exponents are preserved. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- All full physical roots of a prefix block are actual full-prefix roots. -/
theorem originalScheduledFullPhysicalCarrier_subset_prefixRoots (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    (originalScheduledFullPhysicalCarrier bound i.val).carrier ⊆
      (originalScheduledPrefixFullRootCarrier bound k).carrier :=
  fun _ hx => Set.mem_iUnion.mpr ⟨i, hx⟩

/-- The genuine finite native source sum is atomic on the full undeleted roots. -/
theorem originalScheduledNativeSource_sum_atomicOnRoots (bound : ℕ → ℕ) (k : ℕ)
    (r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ) :
    AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k)
      (∑ i : Fin k, originalScheduledNativeSource bound i.val (r i)) := by
  intro f hf
  rw [_root_.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact (originalScheduledNativeSource_atomicOnRoots bound i.val (r i)).mono
    (originalScheduledFullPhysicalCarrier_subset_prefixRoots bound k i) f hf

/-- The original Fourier record of the entire native sum is on the whole common cone. -/
theorem originalScheduledNativeSource_sum_fourier_atomicOnCone (bound : ℕ → ℕ) (k : ℕ)
    (r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ) :
    AtomicOnCarrier (originalScheduledPrefixCone bound k)
      (𝓕 (∑ i : Fin k, originalScheduledNativeSource bound i.val (r i))) := by
  change AtomicOnCarrier _ (temperedFourierLinearMap (∑ i : Fin k, originalScheduledNativeSource bound i.val (r i)))
  rw [map_sum]
  intro f hf
  rw [_root_.sum_apply]
  exact Finset.sum_eq_zero fun i _ => originalScheduledNativeSource_fourier_atomicOnPrefixCone bound k i (r i) f hf

/-- EVERY actual original pair at its original M,N internally reconstructs its
WHOLE root source as the genuine sum of FULL native block sources. -/
theorem originalScheduledPrefixRootSource_eq_native_sum (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    ∃ r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ,
      originalScheduledPrefixRootSource bound k N T hF =
        ∑ i : Fin k, originalScheduledNativeSource bound i.val (r i) := by
  have hpair : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k) :=
    ⟨(mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr ⟨M, hT⟩,
      (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr ⟨N, hF⟩⟩
  obtain ⟨r, hr, _⟩ := originalScheduledPrefixFraction_native_slabs bound k T hpair
  refine ⟨r, ?_⟩
  apply originalFourierPair_cutNumerator_injective
    (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
    (originalScaledModuleFrequencyHom_injective _
      (originalPrivateScale_pos _ (originalScheduledPrefixDenominator_pos bound k)).ne')
    (originalScheduledPrefixIntegerCoefficients bound k) (originalScheduledPrefixIntegerCoefficients_ne_zero bound k)
    (originalScheduledPrefixFullRootCarrier bound k) (originalScheduledPrefixCone bound k)
    (originalScheduledPrefixCone_subset_module bound k) _ _
    (originalScheduledPrefixRootSource_atomicOnRoots bound k M N T hT hF)
    (originalScheduledNativeSource_sum_atomicOnRoots bound k r)
    (originalScheduledPrefixRootSource_fourier_atomicOnCone bound k N T hF)
    (originalScheduledNativeSource_sum_fourier_atomicOnCone bound k r)
    (originalScheduledPrefixIntegerCoefficients_vanishes bound k) 0
  rw [originalScheduledPrefixRootSource_originalFourierArray,
    originalScheduledNativeSource_sum_cutNumerator, ← hr,
    originalScheduledPrefixPositiveNumerator_laurent]
  rfl

/-- The reconstructed actual native sum retains BOTH original cut formulas on
EVERY integer label, including the zero counted only in the positive cut. -/
theorem originalScheduledPrefix_native_sum_both_cuts (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    ∃ r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ,
      originalScheduledPrefixRootSource bound k N T hF =
        ∑ i : Fin k, originalScheduledNativeSource bound i.val (r i) ∧
      let hpair : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k) :=
        ⟨(mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr ⟨M, hT⟩,
          (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr ⟨N, hF⟩⟩
      let L := originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k))
      let u := originalFourierArray L (originalScheduledPrefixCone bound k)
        (∑ i : Fin k, originalScheduledNativeSource bound i.val (r i))
      ∀ n : ℤ × ℤ,
        originalScheduledPrefixNumerator bound k T hpair n =
          annihilatorArrayConvolution (originalScheduledPrefixIntegerCoefficients bound k) (arrayPositiveCut L 0 u) n ∧
        originalScheduledPrefixNumerator bound k T hpair n =
          -annihilatorArrayConvolution (originalScheduledPrefixIntegerCoefficients bound k) (arrayNegativeCut L 0 u) n := by
  obtain ⟨r, hr⟩ := originalScheduledPrefixRootSource_eq_native_sum bound k M N T hT hF
  refine ⟨r, hr, ?_⟩
  dsimp only
  rw [← hr, originalScheduledPrefixRootSource_originalFourierArray]
  intro n
  exact ⟨originalScheduledPrefixNumerator_positive bound k T _ n,
    originalScheduledPrefixNumerator_negative bound k T _ n⟩

/-- On EVERY full block root, the original sum isolation equals that block's
literal coefficient; ALL other actual full blocks vanish there internally. -/
theorem originalScheduledNativeSource_sum_isolation (bound : ℕ → ℕ) (k : ℕ)
    (r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ)
    (i : Fin k) (x : (originalScheduledFullPhysicalCarrier bound i.val).subtype) :
    (∑ j : Fin k, originalScheduledNativeSource bound j.val (r j))
      ((originalScheduledPrefixFullRootCarrier bound k).isolationSchwartz
        ⟨x, originalScheduledFullPhysicalCarrier_subset_prefixRoots bound k i x.property⟩) =
      originalScheduledNativeSource bound i.val (r i)
        ((originalScheduledFullPhysicalCarrier bound i.val).isolationSchwartz x) := by
  classical
  rw [_root_.sum_apply]
  rw [Finset.sum_eq_single i]
  · exact isolationAction_eq_of_carrier_subset
      (originalScheduledFullPhysicalCarrier_subset_prefixRoots bound k i) _
      (atomicOnCarrier_hasLocallyAtomicAction _ _
        (originalScheduledNativeSource_atomicOnRoots bound i.val (r i))) x
  · intro j _ hji
    rw [atomic_isolation_apply_on_larger_carrier _ _
      (originalScheduledFullPhysicalCarrier_subset_prefixRoots bound k j) _
      (originalScheduledNativeSource_atomicOnRoots bound j.val (r j))]
    have hx : (x : ℝ) ∉ (originalScheduledFullPhysicalCarrier bound j.val).carrier := by
      intro hj
      exact Set.disjoint_left.mp (originalScheduledFullPhysicalCarrier_pairwise_disjoint bound
        (fun h => hji (Fin.ext h).symm)) x.property hj
    exact dite_eq_right hx
  · simp

/-- Deletion of an actual original root forces the corresponding individual
native source coefficient to vanish, AFTER genuine whole-sum reconstruction. -/
theorem originalScheduledPrefixRootSource_native_sum_deleted_roots (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    ∃ r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ,
      originalScheduledPrefixRootSource bound k N T hF =
        ∑ i : Fin k, originalScheduledNativeSource bound i.val (r i) ∧
      ∀ (i : Fin k) (x : (originalScheduledFullPhysicalCarrier bound i.val).subtype),
        (x : ℝ) ∉ (originalScheduledPrefixCarrier bound k).carrier →
        originalScheduledNativeSource bound i.val (r i)
          ((originalScheduledFullPhysicalCarrier bound i.val).isolationSchwartz x) = 0 := by
  obtain ⟨r, hr⟩ := originalScheduledPrefixRootSource_eq_native_sum bound k M N T hT hF
  refine ⟨r, hr, ?_⟩
  intro i x hx
  rw [← originalScheduledNativeSource_sum_isolation bound k r i x, ← hr]
  exact originalScheduledPrefixRootSource_deleted_root_zero bound k M N T hT hF _ hx

/-- EVERY member of the COMPLETE actual original prefix strong space has a
genuine full native source sum and cone/root companion, retaining BOTH original
strong exponents and all literal physical deleted-root equations internally. -/
theorem originalScheduledPrefix_complete_native_source_decomposition (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ,
    ∃ M N : ℕ,
      let ρ := ∑ i : Fin k, originalScheduledNativeSource bound i.val (r i)
      AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k) ρ ∧
      AtomicOnCarrier (originalScheduledPrefixCone bound k) (𝓕 ρ) ∧
      AtomicOnCarrier (originalScheduledPrefixCone bound k) (T - ρ) ∧
      AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k) (𝓕 (T - ρ)) ∧
      ρ ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M ∧
      𝓕 ρ ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N ∧
      T - ρ ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M ∧
      𝓕 (T - ρ) ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N ∧
      ∀ (i : Fin k) (x : (originalScheduledFullPhysicalCarrier bound i.val).subtype),
        (x : ℝ) ∉ (originalScheduledPrefixCarrier bound k).carrier →
        originalScheduledNativeSource bound i.val (r i)
          ((originalScheduledFullPhysicalCarrier bound i.val).isolationSchwartz x) = 0 := by
  obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT.1
  obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hT.2
  have hM' : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M := hM
  have hN' : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N := hN
  obtain ⟨r, hr, hz⟩ := originalScheduledPrefixRootSource_native_sum_deleted_roots bound k M N T hM' hN'
  refine ⟨r, M, N, ?_⟩
  dsimp only
  rw [← hr]
  have hρ := originalScheduledPrefixRootSource_both_original_strong bound k M N T hM' hN'
  have hC := originalScheduledPrefixRootSource_complement_both_original_strong bound k M N T hM' hN'
  exact ⟨originalScheduledPrefixRootSource_atomicOnRoots bound k M N T hM' hN',
    originalScheduledPrefixRootSource_fourier_atomicOnCone bound k N T hN',
    originalScheduledPrefixRootSource_complement_atomicOnCone bound k M N T hM' hN',
    originalScheduledPrefixRootSource_complement_fourier_atomicOnRoots bound k N T hN',
    hρ.1, hρ.2, hC.1, hC.2, hz⟩

end
end MeyerGeneralProblem.StrongParity
