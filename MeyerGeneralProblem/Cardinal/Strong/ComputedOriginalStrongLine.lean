module

public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalSelectedKernel

@[expose] public section

/-! Complete ORIGINAL strongly tempered pair line for the PARTICULAR deletion
labels returned by the terminating program. Parameters, full head, whole W
basis, determinant and termination are supplied internally. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped FourierTransform

/-- Actual finite original roots deleted by the internally terminating search. -/
def coupledComputedOriginalSelectedRootPoints (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    Finset (compactOriginalProductSheetCarrier (coupledCompactOriginalParameterBlock scales hpos offset s)).subtype :=
  computedOriginalSelectedRootPoints (coupledCompactOriginalParameterBlock scales hpos offset s) hs m
    (coupledComputedOriginalWSelectedRoots scales hpos offset s hs m).1

/-- Actual original physical deletion set supplied by the implemented finite search. -/
def coupledComputedOriginalPhysicalDeletion (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) : Set ℝ :=
  computedOriginalSelectedPhysicalDeletion (coupledCompactOriginalParameterBlock scales hpos offset s) hs m
    (coupledComputedOriginalWSelectedRoots scales hpos offset s hs m).1

/-- The actual computed root deletions retain the exact complete original W cardinal equation. -/
theorem coupledComputedOriginalSelectedRootPoints_card (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    (coupledComputedOriginalSelectedRootPoints scales hpos offset s hs m).card +
      (computedOriginalNoncoarseHeadLabels s m).card + 2 = (s + 1) ^ 2 :=
  computedOriginalSelectedRootPoints_card _ hs m _
    (coupledComputedOriginalWSelectedRoots_spec scales hpos offset s hs m).1

/-- The computed original physical deletion set is finite. -/
theorem coupledComputedOriginalPhysicalDeletion_finite (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m).Finite :=
  CompactOriginal.productSelectedPhysicalDeletion_finite _ _

/-- THIS implemented finite deletion set yields the COMPLETE original strong pair line.
No supplied rank, search certificate or constructed-image premise is assumed. -/
theorem coupledComputedOriginalStrongPair_complete_line (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    Module.finrank ℂ (CompactOriginal.productOriginalStrongDeletedPairSpace
      (coupledCompactOriginalParameterBlock scales hpos offset s)
      (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m))) = 1 ∧
    ∃ r : productNumeratorIndex s → ℂ,
      r ∈ CompactOriginal.productOriginalDeletionKernel
        (coupledCompactOriginalParameterBlock scales hpos offset s)
        (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
        (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) ∧
      productCornerFunctional s r = 1 :=
  computedOriginalSelectedRoot_complete_pair_line _ hs m _
    (coupledComputedOriginalWSelectedRoots_spec scales hpos offset s hs m).2

/-- The actual normalized finite slab numerator of the complete computed strong pair line. -/
def coupledComputedOriginalLineNumerator (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) : productNumeratorIndex s → ℂ :=
  Classical.choose (coupledComputedOriginalStrongPair_complete_line scales hpos offset s hs m).2

/-- The normalized numerator satisfies EVERY original deletion row and literal J=1. -/
theorem coupledComputedOriginalLineNumerator_spec (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    coupledComputedOriginalLineNumerator scales hpos offset s hs m ∈
      CompactOriginal.productOriginalDeletionKernel
        (coupledCompactOriginalParameterBlock scales hpos offset s)
        (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
        (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) ∧
    productCornerFunctional s (coupledComputedOriginalLineNumerator scales hpos offset s hs m) = 1 :=
  Classical.choose_spec (coupledComputedOriginalStrongPair_complete_line scales hpos offset s hs m).2

/-- Nonzero actual original physical source of the complete computed strong line. -/
def coupledComputedOriginalLineSource (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) : TemperedDistribution ℝ ℂ :=
  CompactOriginal.productPhysicalDistribution (coupledCompactOriginalParameterBlock scales hpos offset s)
    (coupledComputedOriginalLineNumerator scales hpos offset s hs m)

/-- The actual normalized original source is nonzero. -/
theorem coupledComputedOriginalLineSource_ne_zero (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    coupledComputedOriginalLineSource scales hpos offset s hs m ≠ 0 := by
  intro hz
  have hr : coupledComputedOriginalLineNumerator scales hpos offset s hs m = 0 :=
    (CompactOriginal.productPhysicalDistribution_injective
      (coupledCompactOriginalParameterBlock scales hpos offset s))
      (hz.trans (CompactOriginal.productPhysicalDistributionLinearMap _).map_zero.symm)
  have hj := (coupledComputedOriginalLineNumerator_spec scales hpos offset s hs m).2
  rw [hr, map_zero] at hj
  exact zero_ne_one hj

/-- The literal J=1 normalization uniquely determines the numerator in the ENTIRE kernel. -/
theorem coupledComputedOriginalLineNumerator_unique (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (r : productNumeratorIndex s → ℂ)
    (hr : r ∈ CompactOriginal.productOriginalDeletionKernel
      (coupledCompactOriginalParameterBlock scales hpos offset s)
      (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m)))
    (hj : productCornerFunctional s r = 1) :
    r = coupledComputedOriginalLineNumerator scales hpos offset s hs m := by
  have hdim : Module.finrank ℂ (CompactOriginal.productOriginalDeletionKernel
      (coupledCompactOriginalParameterBlock scales hpos offset s)
      (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m))) = 1 := by
    rw [← CompactOriginal.productOriginalStrongDeletedPairSpace_finrank_eq_kernel]
    exact (coupledComputedOriginalStrongPair_complete_line scales hpos offset s hs m).1
  have hnum := coupledComputedOriginalLineNumerator_spec scales hpos offset s hs m
  have hn : coupledComputedOriginalLineNumerator scales hpos offset s hs m ≠ 0 := by
    intro hz
    have hh := hnum.2
    rw [hz, map_zero] at hh
    exact zero_ne_one hh
  have hk := eq_span_singleton_of_mem_of_finrank_eq_one hdim hnum.1 hn
  have hmem : r ∈ Submodule.span ℂ {coupledComputedOriginalLineNumerator scales hpos offset s hs m} :=
    hk ▸ hr
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc1 : c = 1 := by
    have hh := congrArg (productCornerFunctional s) hc
    simpa only [map_smul, smul_eq_mul, hnum.2, mul_one, hj] using hh
  simpa only [hc1, one_smul] using hc.symm

/-- EVERY original strongly tempered deleted-support pair is exactly a scalar
multiple of the normalized computed source. Both strong records are retained. -/
theorem coupledComputedOriginalStrongPair_complete_span (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (T : TemperedDistribution ℝ ℂ) :
    T ∈ CompactOriginal.productOriginalStrongDeletedPairSpace
      (coupledCompactOriginalParameterBlock scales hpos offset s)
      (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) ↔
      ∃ c : ℂ, T = c • coupledComputedOriginalLineSource scales hpos offset s hs m := by
  rw [CompactOriginal.productOriginalStrongDeletedPairSpace_eq_pair]
  apply CompactOriginal.productOriginalGapLine_complete_span
  · rw [← CompactOriginal.productOriginalStrongDeletedPairSpace_finrank_eq_kernel]
    exact (coupledComputedOriginalStrongPair_complete_line scales hpos offset s hs m).1
  · exact (coupledComputedOriginalLineNumerator_spec scales hpos offset s hs m).1
  · exact (coupledComputedOriginalLineNumerator_spec scales hpos offset s hs m).2

/-- The computed source is admitted on both ACTUAL original deleted carriers,
with the existing polynomial absolute total-variation exponents. -/
theorem coupledComputedOriginalLineSource_both_strong (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    coupledComputedOriginalLineSource scales hpos offset s hs m ∈
      stronglyTemperedAtomicAtExponent
        ((compactOriginalProductSheetCarrier (coupledCompactOriginalParameterBlock scales hpos offset s)).delete
          (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)) ((s - 1) + 2) ∧
    𝓕 (coupledComputedOriginalLineSource scales hpos offset s hs m) ∈
      stronglyTemperedAtomicAtExponent
        (spectralConeCarrier.delete (productOriginalHeadDeletion s (computedOriginalHeadMask s m))) (s + 3) := by
  let T : CompactOriginal.productOriginalDeletedPairSpace
      (coupledCompactOriginalParameterBlock scales hpos offset s)
      (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) :=
    ⟨coupledComputedOriginalLineSource scales hpos offset s hs m,
      (CompactOriginal.productPhysical_mem_deletedPairSpace_iff _ _ _ _).mpr
        (coupledComputedOriginalLineNumerator_spec scales hpos offset s hs m).1⟩
  exact ⟨CompactOriginal.productOriginalDeletedPair_physical_mem_strongExponent _ _ _ T,
    CompactOriginal.productOriginalDeletedPair_spectral_mem_strongExponent _ _ _ T⟩

/-- The ACTUAL computed source fails every physical weighted-TV exponent N<s,
including after the selected root deletions. -/
theorem coupledComputedOriginalLineSource_not_lowExponent (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m N : ℕ) (hN : N < s) :
    coupledComputedOriginalLineSource scales hpos offset s hs m ∉
      stronglyTemperedAtomicAtExponent
        ((compactOriginalProductSheetCarrier (coupledCompactOriginalParameterBlock scales hpos offset s)).delete
          (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)) N :=
  CompactOriginal.productOriginalGapLine_not_strongExponent _ ⟨0, by omega⟩ _ _
    (by rw [(coupledComputedOriginalLineNumerator_spec scales hpos offset s hs m).2]; exact one_ne_zero)
    N (by omega)

/-- EVERY nonzero member of the COMPLETE computed strong pair line fails N<s.
This is not merely an obstruction for the chosen source. -/
theorem coupledComputedOriginalStrongPair_not_lowExponent (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m N : ℕ) (hN : N < s) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ CompactOriginal.productOriginalStrongDeletedPairSpace
      (coupledCompactOriginalParameterBlock scales hpos offset s)
      (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m))) (hT0 : T ≠ 0) :
    T ∉ stronglyTemperedAtomicAtExponent
      ((compactOriginalProductSheetCarrier (coupledCompactOriginalParameterBlock scales hpos offset s)).delete
        (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)) N := by
  obtain ⟨c, rfl⟩ := (coupledComputedOriginalStrongPair_complete_span scales hpos offset s hs m T).mp hT
  have hc : c ≠ 0 := by
    intro hz
    apply hT0
    rw [hz]
    exact zero_smul ℂ (coupledComputedOriginalLineSource scales hpos offset s hs m)
  intro h
  have hh := (stronglyTemperedAtomicAtExponent _ N).smul_mem c⁻¹ h
  have hs' : coupledComputedOriginalLineSource scales hpos offset s hs m ∈
      stronglyTemperedAtomicAtExponent
        ((compactOriginalProductSheetCarrier (coupledCompactOriginalParameterBlock scales hpos offset s)).delete
          (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)) N := by
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh
  exact coupledComputedOriginalLineSource_not_lowExponent scales hpos offset s hs m N hN hs'

end

end MeyerGeneralProblem.StrongParity
