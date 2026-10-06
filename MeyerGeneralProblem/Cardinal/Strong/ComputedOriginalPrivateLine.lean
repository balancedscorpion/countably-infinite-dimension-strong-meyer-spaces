module

public import MeyerGeneralProblem.Cardinal.Strong.PrivateOriginalDeletions
public import MeyerGeneralProblem.Cardinal.Strong.PrivatePrimeSchedule

@[expose] public section

/-! Complete ORIGINAL strong directed lines on the literal private-scale
allowed carriers. These are the directed blocks for the final common carrier;
full common-carrier mixed-source and infinite exhaustion remain separate. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped FourierTransform

/-- The COMPLETE original strong pair space on BOTH literal private carriers. -/
def coupledComputedOriginalPrivateStrongPair (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  StronglyTemperedAtomicOnCarrier
    (coupledComputedOriginalPrivatePhysicalCarrier scales hpos offset s hs m hm) ⊓
  (StronglyTemperedAtomicOnCarrier (computedOriginalPrivateSpectralCarrier s m hm)).comap
    temperedFourierLinearMap

/-- Whole original pair membership is transported, for EVERY distribution. -/
theorem coupledComputedOriginalPrivateStrongPair_dilation_iff (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m)
    (T : TemperedDistribution ℝ ℂ) :
    combDistributionDilation (originalPrivateScale m) (originalPrivateScale_pos m hm).ne' T ∈
      coupledComputedOriginalPrivateStrongPair scales hpos offset s hs m hm ↔
    T ∈ CompactOriginal.productOriginalStrongDeletedPairSpace
      (coupledCompactOriginalParameterBlock scales hpos offset s)
      (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) := by
  unfold coupledComputedOriginalPrivateStrongPair
  rw [coupledComputedOriginalPrivatePhysicalCarrier_eq_dilate scales hpos offset s hs m hm,
    computedOriginalPrivateSpectralCarrier_eq_dilate s m hm]
  change (combDistributionDilation (originalPrivateScale m) (originalPrivateScale_pos m hm).ne' T ∈
    StronglyTemperedAtomicOnCarrier _ ∧
    𝓕 (combDistributionDilation (originalPrivateScale m) (originalPrivateScale_pos m hm).ne' T) ∈
      StronglyTemperedAtomicOnCarrier _) ↔
    T ∈ StronglyTemperedAtomicOnCarrier _ ∧ 𝓕 T ∈ StronglyTemperedAtomicOnCarrier _
  rw [stronglyTemperedAtomicOnCarrier_dilation_iff _ _ (originalPrivateScale_pos m hm) T,
    stronglyTemperedAtomicOnCarrier_fourier_dilation_iff _ _ (originalPrivateScale_pos m hm) T]

/-- The COMPLETE original native strong line is equivalent to the COMPLETE
literal private strong line, with all allowed points and original support rows. -/
def coupledComputedOriginalPrivateStrongPairEquiv (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) :
    CompactOriginal.productOriginalStrongDeletedPairSpace
      (coupledCompactOriginalParameterBlock scales hpos offset s)
      (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) ≃ₗ[ℂ]
        coupledComputedOriginalPrivateStrongPair scales hpos offset s hs m hm := by
  rw [coupledComputedOriginalPrivateStrongPair,
    coupledComputedOriginalPrivatePhysicalCarrier_eq_dilate scales hpos offset s hs m hm,
    computedOriginalPrivateSpectralCarrier_eq_dilate s m hm]
  exact originalStrongPairDilationEquiv _ _ _ (originalPrivateScale_pos m hm)

theorem coupledComputedOriginalPrivateStrongPair_finrank_one (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) :
    Module.finrank ℂ (coupledComputedOriginalPrivateStrongPair scales hpos offset s hs m hm) = 1 := by
  rw [← (coupledComputedOriginalPrivateStrongPairEquiv scales hpos offset s hs m hm).finrank_eq]
  exact (coupledComputedOriginalStrongPair_complete_line scales hpos offset s hs m).1

/-- The nonzero ORIGINAL source, with genuine distributional private dilation. -/
def coupledComputedOriginalPrivateLineSource (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) : TemperedDistribution ℝ ℂ :=
  combDistributionDilation (originalPrivateScale m) (originalPrivateScale_pos m hm).ne'
    (coupledComputedOriginalLineSource scales hpos offset s hs m)

theorem coupledComputedOriginalPrivateLineSource_ne_zero (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) :
    coupledComputedOriginalPrivateLineSource scales hpos offset s hs m hm ≠ 0 := by
  intro hz
  apply coupledComputedOriginalLineSource_ne_zero scales hpos offset s hs m
  have h := congrArg (combDistributionDilation (originalPrivateScale m)⁻¹
    (inv_ne_zero (originalPrivateScale_pos m hm).ne')) hz
  simpa only [coupledComputedOriginalPrivateLineSource, combDistributionDilation_inv_apply, map_zero] using h

/-- EVERY original supported private pair is a scalar multiple of the actual
source. The reverse implication also supplies BOTH original strong records. -/
theorem coupledComputedOriginalPrivateStrongPair_complete_span (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m)
    (T : TemperedDistribution ℝ ℂ) :
    T ∈ coupledComputedOriginalPrivateStrongPair scales hpos offset s hs m hm ↔
      ∃ a : ℂ, T = a • coupledComputedOriginalPrivateLineSource scales hpos offset s hs m hm := by
  let e := combDistributionDilationLinearEquiv (originalPrivateScale m) (originalPrivateScale_pos m hm)
  constructor
  · intro hT
    let U := e.symm T
    have he : combDistributionDilation (originalPrivateScale m) (originalPrivateScale_pos m hm).ne' U = T :=
      e.apply_symm_apply T
    have hU := (coupledComputedOriginalPrivateStrongPair_dilation_iff scales hpos offset s hs m hm U).mp
      (he.symm ▸ hT)
    obtain ⟨a, ha⟩ := (coupledComputedOriginalStrongPair_complete_span scales hpos offset s hs m U).mp hU
    refine ⟨a, ?_⟩
    rw [← he, ha, map_smul]
    rfl
  · rintro ⟨a, rfl⟩
    have hU := (coupledComputedOriginalStrongPair_complete_span scales hpos offset s hs m
      (a • coupledComputedOriginalLineSource scales hpos offset s hs m)).mpr ⟨a, rfl⟩
    have h := (coupledComputedOriginalPrivateStrongPair_dilation_iff scales hpos offset s hs m hm _).mpr hU
    simpa only [map_smul, coupledComputedOriginalPrivateLineSource] using h

theorem coupledComputedOriginalPrivateLineSource_both_strong (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) :
    coupledComputedOriginalPrivateLineSource scales hpos offset s hs m hm ∈
      stronglyTemperedAtomicAtExponent
        (coupledComputedOriginalPrivatePhysicalCarrier scales hpos offset s hs m hm) ((s - 1) + 2) ∧
    𝓕 (coupledComputedOriginalPrivateLineSource scales hpos offset s hs m hm) ∈
      stronglyTemperedAtomicAtExponent (computedOriginalPrivateSpectralCarrier s m hm) (s + 3) := by
  rw [coupledComputedOriginalPrivatePhysicalCarrier_eq_dilate scales hpos offset s hs m hm,
    computedOriginalPrivateSpectralCarrier_eq_dilate s m hm]
  exact ⟨stronglyTemperedAtomicAtExponent_combDistributionDilation _ _ (originalPrivateScale_pos m hm) _ _
    (coupledComputedOriginalLineSource_both_strong scales hpos offset s hs m).1,
    (stronglyTemperedAtomicAtExponent_fourier_dilation_iff _ _ (originalPrivateScale_pos m hm) _ _).mpr
      (coupledComputedOriginalLineSource_both_strong scales hpos offset s hs m).2⟩

/-- EVERY nonzero member of the COMPLETE private strong line fails N<s on
its original physical record; no particular-source or cancellation proxy is used. -/
theorem coupledComputedOriginalPrivateStrongPair_not_lowExponent (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m)
    (N : ℕ) (hN : N < s) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ coupledComputedOriginalPrivateStrongPair scales hpos offset s hs m hm) (hT0 : T ≠ 0) :
    T ∉ stronglyTemperedAtomicAtExponent
      (coupledComputedOriginalPrivatePhysicalCarrier scales hpos offset s hs m hm) N := by
  let e := combDistributionDilationLinearEquiv (originalPrivateScale m) (originalPrivateScale_pos m hm)
  let U := e.symm T
  have he : combDistributionDilation (originalPrivateScale m) (originalPrivateScale_pos m hm).ne' U = T :=
    e.apply_symm_apply T
  have hU := (coupledComputedOriginalPrivateStrongPair_dilation_iff scales hpos offset s hs m hm U).mp
    (he.symm ▸ hT)
  have hU0 : U ≠ 0 := by
    intro hz
    apply hT0
    rw [← he, hz]
    exact map_zero _
  intro hlow
  rw [coupledComputedOriginalPrivatePhysicalCarrier_eq_dilate scales hpos offset s hs m hm, ← he] at hlow
  exact coupledComputedOriginalStrongPair_not_lowExponent scales hpos offset s hs m N hN U hU hU0
    ((stronglyTemperedAtomicAtExponent_dilation_iff _ _ (originalPrivateScale_pos m hm) N U).mp hlow)

/-- Both literal private original records have finite weighted variation at N. -/
def coupledComputedOriginalPrivateExponentLayer (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) (N : ℕ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  stronglyTemperedAtomicAtExponent
    (coupledComputedOriginalPrivatePhysicalCarrier scales hpos offset s hs m hm) N ⊓
  (stronglyTemperedAtomicAtExponent (computedOriginalPrivateSpectralCarrier s m hm) N).comap
    temperedFourierLinearMap

theorem coupledComputedOriginalPrivateExponentLayer_le_strongPair (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) (N : ℕ) :
    coupledComputedOriginalPrivateExponentLayer scales hpos offset s hs m hm N ≤
      coupledComputedOriginalPrivateStrongPair scales hpos offset s hs m hm := by
  intro T hT
  exact ⟨(mem_stronglyTemperedAtomicOnCarrier_iff _ T).mpr ⟨N, hT.1⟩,
    (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mpr ⟨N, hT.2⟩⟩

theorem coupledComputedOriginalPrivateExponentLayer_eq_bot_of_lt (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m)
    (N : ℕ) (hN : N < s) :
    coupledComputedOriginalPrivateExponentLayer scales hpos offset s hs m hm N = ⊥ := by
  apply le_antisymm _ bot_le
  intro T hT
  apply (Submodule.mem_bot ℂ).mpr
  by_contra hn
  exact coupledComputedOriginalPrivateStrongPair_not_lowExponent scales hpos offset s hs m hm N hN T
    (coupledComputedOriginalPrivateExponentLayer_le_strongPair scales hpos offset s hs m hm N hT) hn hT.1

/-- At N≥s+3 EVERY original private strong pair is admitted at that exponent. -/
theorem coupledComputedOriginalPrivateExponentLayer_eq_strongPair_of_ge (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m)
    (N : ℕ) (hN : s + 3 ≤ N) :
    coupledComputedOriginalPrivateExponentLayer scales hpos offset s hs m hm N =
      coupledComputedOriginalPrivateStrongPair scales hpos offset s hs m hm := by
  apply le_antisymm (coupledComputedOriginalPrivateExponentLayer_le_strongPair scales hpos offset s hs m hm N)
  intro T hT
  obtain ⟨a, rfl⟩ := (coupledComputedOriginalPrivateStrongPair_complete_span scales hpos offset s hs m hm T).mp hT
  have hsource := coupledComputedOriginalPrivateLineSource_both_strong scales hpos offset s hs m hm
  constructor
  · exact (stronglyTemperedAtomicAtExponent _ N).smul_mem a
      (stronglyTemperedAtomicAtExponent_mono _ (by omega) hsource.1)
  · change 𝓕 (a • coupledComputedOriginalPrivateLineSource scales hpos offset s hs m hm) ∈
      stronglyTemperedAtomicAtExponent (computedOriginalPrivateSpectralCarrier s m hm) N
    rw [FourierTransform.fourier_smul]
    exact (stronglyTemperedAtomicAtExponent _ N).smul_mem a
      (stronglyTemperedAtomicAtExponent_mono _ hN hsource.2)

theorem coupledComputedOriginalPrivateExponentLayer_finrank_one_of_ge (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m)
    (N : ℕ) (hN : s + 3 ≤ N) :
    Module.finrank ℂ (coupledComputedOriginalPrivateExponentLayer scales hpos offset s hs m hm N) = 1 := by
  rw [coupledComputedOriginalPrivateExponentLayer_eq_strongPair_of_ge scales hpos offset s hs m hm N hN]
  exact coupledComputedOriginalPrivateStrongPair_finrank_one scales hpos offset s hs m hm

theorem coupledComputedOriginalPrivateExponentLayer_finiteDimensional (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) (N : ℕ) :
    FiniteDimensional ℂ (coupledComputedOriginalPrivateExponentLayer scales hpos offset s hs m hm N) := by
  let : FiniteDimensional ℂ (coupledComputedOriginalPrivateStrongPair scales hpos offset s hs m hm) :=
    FiniteDimensional.of_finrank_pos (by
      rw [coupledComputedOriginalPrivateStrongPair_finrank_one scales hpos offset s hs m hm]
      norm_num)
  exact Submodule.finiteDimensional_of_le
    (coupledComputedOriginalPrivateExponentLayer_le_strongPair scales hpos offset s hs m hm N)

end

end MeyerGeneralProblem.StrongParity
