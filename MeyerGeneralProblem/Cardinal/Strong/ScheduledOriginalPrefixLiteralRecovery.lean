module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixCompanionRecovery
public import MeyerGeneralProblem.Distribution.LiteralAtomicSourceRecovery

@[expose] public section

/-! GENUINE actual root/cone recovery precedes literal restrictions. Every
actual original strong mixed-prefix pair now has its root piece identified as
the original record, and BOTH original variations survive at the SAME exponents. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- Actual FULL roots and the whole common cone are disjoint internally. -/
theorem originalScheduledPrefixFullRoots_disjoint_cone (bound : ℕ → ℕ) (k : ℕ) :
    Disjoint (originalScheduledPrefixFullRootCarrier bound k).carrier
      (originalScheduledPrefixCone bound k).carrier := by
  apply Set.disjoint_left.mpr
  intro x hx hc
  exact originalScheduledPrefixRootSet_not_mem_module bound k x hx
    (originalScheduledPrefixModuleSet_subset_rational_module bound k
      (originalScheduledPrefixCone_subset_module bound k hc))

/-- The recovered GENUINE source equals the ORIGINAL literal physical root part,
only AFTER its complementary actual cone/root pair has been recovered. -/
theorem originalScheduledPrefixRootSource_eq_literal (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    originalScheduledPrefixRootSource bound k N T hF =
      originalWeightedAtomicRestriction (originalScheduledPrefixCarrier bound k)
        (originalScheduledPrefixFullRootCarrier bound k).carrier M T hT :=
  atomic_source_eq_originalWeightedAtomicRestriction _ _ _
    (originalScheduledPrefixFullRoots_disjoint_cone bound k) M T _ hT
    (originalScheduledPrefixRootSource_atomicOnRoots bound k M N T hT hF)
    (originalScheduledPrefixRootSource_complement_atomicOnCone bound k M N T hT hF)

/-- The recovered physical source retains ORIGINAL variation at exactly the SAME M. -/
theorem originalScheduledPrefixRootSource_mem_strongExponent (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    originalScheduledPrefixRootSource bound k N T hF ∈
      stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M := by
  rw [originalScheduledPrefixRootSource_eq_literal bound k M N T hT hF]
  exact originalWeightedAtomicRestriction_mem_strongExponent _ _ _ _ _

/-- At EVERY original physical carrier point, the actual source coefficient is
the ORIGINAL coefficient on roots and zero on the complete cone. -/
theorem originalScheduledPrefixRootSource_isolation (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N)
    (x : (originalScheduledPrefixCarrier bound k).subtype) :
    originalScheduledPrefixRootSource bound k N T hF
        ((originalScheduledPrefixCarrier bound k).isolationSchwartz x) =
      originalAtomicRestrictionCoefficient (originalScheduledPrefixCarrier bound k)
        (originalScheduledPrefixFullRootCarrier bound k).carrier T x := by
  rw [originalScheduledPrefixRootSource_eq_literal bound k M N T hT hF]
  exact originalWeightedAtomicRestriction_isolation _ _ _ _ _ x

/-- EVERY original weighted physical source term is bounded by the ORIGINAL
term at the SAME exponent, without a reflected weight or surrogate record. -/
theorem originalScheduledPrefixRootSource_weight_le (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N)
    (x : (originalScheduledPrefixCarrier bound k).subtype) :
    stronglyTemperedCoefficientTerm (originalScheduledPrefixCarrier bound k) M
      (originalScheduledPrefixRootSource bound k N T hF) x ≤
        stronglyTemperedCoefficientTerm (originalScheduledPrefixCarrier bound k) M T x := by
  unfold stronglyTemperedCoefficientTerm
  rw [originalScheduledPrefixRootSource_isolation bound k M N T hT hF]
  exact originalAtomicRestrictionCoefficient_weight_le _ _ M T x

/-- The GENUINE source has BOTH original strong records at the original M and N. -/
theorem originalScheduledPrefixRootSource_both_original_strong (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    originalScheduledPrefixRootSource bound k N T hF ∈
      stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M ∧
    𝓕 (originalScheduledPrefixRootSource bound k N T hF) ∈
      stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N := by
  refine ⟨originalScheduledPrefixRootSource_mem_strongExponent bound k M N T hT hF, ?_⟩
  rw [originalScheduledPrefixRootSource_fourier]
  exact originalScheduledPrefixModuleSpectralRecord_mem_strongExponent bound k N T hF

/-- Subtraction retains BOTH ORIGINAL weighted records at the SAME original exponents. -/
theorem originalScheduledPrefixRootSource_complement_both_original_strong (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    T - originalScheduledPrefixRootSource bound k N T hF ∈
      stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M ∧
    𝓕 (T - originalScheduledPrefixRootSource bound k N T hF) ∈
      stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N := by
  have h := originalScheduledPrefixRootSource_both_original_strong bound k M N T hT hF
  refine ⟨(stronglyTemperedAtomicAtExponent _ M).sub_mem hT h.1, ?_⟩
  change temperedFourierLinearMap (T - originalScheduledPrefixRootSource bound k N T hF) ∈ _
  rw [map_sub, temperedFourierLinearMap_apply, temperedFourierLinearMap_apply]
  exact (stronglyTemperedAtomicAtExponent _ N).sub_mem hF h.2

/-- Every FULL root deleted from the ORIGINAL common carrier has its actual
recovered-source coefficient zero; deletion is a conclusion of literal recovery. -/
theorem originalScheduledPrefixRootSource_deleted_root_zero (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N)
    (x : (originalScheduledPrefixFullRootCarrier bound k).subtype)
    (hx : (x : ℝ) ∉ (originalScheduledPrefixCarrier bound k).carrier) :
    originalScheduledPrefixRootSource bound k N T hF
      ((originalScheduledPrefixFullRootCarrier bound k).isolationSchwartz x) = 0 :=
  atomic_isolation_eq_zero_off_other_carrier _ _ _
    (originalScheduledPrefixRootSource_atomicOnRoots bound k M N T hT hF)
    (hasLocallyAtomicAction_atomicOnCarrier _ _
      (originalScheduledPrefixRootSource_mem_strongExponent bound k M N T hT hF).1) x hx

/-- Source and companion physical terms partition the ORIGINAL variation at SAME M exactly. -/
theorem originalScheduledPrefixRootSource_physical_weight_partition (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N)
    (x : (originalScheduledPrefixCarrier bound k).subtype) :
    stronglyTemperedCoefficientTerm (originalScheduledPrefixCarrier bound k) M
      (originalScheduledPrefixRootSource bound k N T hF) x +
    stronglyTemperedCoefficientTerm (originalScheduledPrefixCarrier bound k) M
      (T - originalScheduledPrefixRootSource bound k N T hF) x =
    stronglyTemperedCoefficientTerm (originalScheduledPrefixCarrier bound k) M T x := by
  rw [originalScheduledPrefixRootSource_eq_literal bound k M N T hT hF]
  exact originalWeightedAtomicRestriction_weight_partition _ _ _ _ _ x

/-- Source and companion spectral terms partition the ORIGINAL variation at SAME N exactly. -/
theorem originalScheduledPrefixRootSource_spectral_weight_partition (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N)
    (x : (originalScheduledPrefixCarrier bound k).subtype) :
    stronglyTemperedCoefficientTerm (originalScheduledPrefixCarrier bound k) N
      (𝓕 (originalScheduledPrefixRootSource bound k N T hF)) x +
    stronglyTemperedCoefficientTerm (originalScheduledPrefixCarrier bound k) N
      (𝓕 (T - originalScheduledPrefixRootSource bound k N T hF)) x =
    stronglyTemperedCoefficientTerm (originalScheduledPrefixCarrier bound k) N (𝓕 T) x := by
  change stronglyTemperedCoefficientTerm _ N (𝓕 (originalScheduledPrefixRootSource bound k N T hF)) x +
    stronglyTemperedCoefficientTerm _ N (temperedFourierLinearMap (T - originalScheduledPrefixRootSource bound k N T hF)) x = _
  rw [map_sub, temperedFourierLinearMap_apply, temperedFourierLinearMap_apply,
    originalScheduledPrefixRootSource_fourier]
  exact originalWeightedAtomicRestriction_weight_partition _ _ _ _ _ x

/-- EVERY complete ORIGINAL strong mixed-prefix pair decomposes into GENUINE
root/cone and cone/root pairs in the SAME complete original strong space.
All exponents, simple-root, annihilation and coset inputs are supplied internally. -/
theorem originalScheduledPrefix_complete_strong_pair_decomposition (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ ρ : TemperedDistribution ℝ ℂ,
      AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k) ρ ∧
      AtomicOnCarrier (originalScheduledPrefixCone bound k) (𝓕 ρ) ∧
      AtomicOnCarrier (originalScheduledPrefixCone bound k) (T - ρ) ∧
      AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k) (𝓕 (T - ρ)) ∧
      ρ ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k) ∧
      T - ρ ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k) := by
  obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT.1
  obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hT.2
  have hM' : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M := hM
  have hN' : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N := hN
  have hρ := originalScheduledPrefixRootSource_both_original_strong bound k M N T hM' hN'
  have hC := originalScheduledPrefixRootSource_complement_both_original_strong bound k M N T hM' hN'
  refine ⟨originalScheduledPrefixRootSource bound k N T hN',
    originalScheduledPrefixRootSource_atomicOnRoots bound k M N T hM' hN',
    originalScheduledPrefixRootSource_fourier_atomicOnCone bound k N T hN',
    originalScheduledPrefixRootSource_complement_atomicOnCone bound k M N T hM' hN',
    originalScheduledPrefixRootSource_complement_fourier_atomicOnRoots bound k N T hN', ?_, ?_⟩
  · exact ⟨(mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr ⟨M, hρ.1⟩,
      (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr ⟨N, hρ.2⟩⟩
  · exact ⟨(mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr ⟨M, hC.1⟩,
      (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr ⟨N, hC.2⟩⟩

end
end MeyerGeneralProblem.StrongParity
