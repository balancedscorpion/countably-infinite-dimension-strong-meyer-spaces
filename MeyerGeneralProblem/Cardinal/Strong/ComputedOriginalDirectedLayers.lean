module

public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalStrongLine
public import MeyerGeneralProblem.Cardinal.StrongFiltration

@[expose] public section

/-! Complete two-carrier ORIGINAL weighted absolute-mass layers for the computed
one-block line. These are directed block layers, not the final COMMON-carrier
StrongMeyerExponentLayer. No exact minimum order inside [s,s+3] is claimed. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped FourierTransform

/-- Both actual original deleted records have summable weighted variation at N. -/
def coupledComputedOriginalDirectedExponentLayer (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m N : ℕ) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  stronglyTemperedAtomicAtExponent
    ((compactOriginalProductSheetCarrier (coupledCompactOriginalParameterBlock scales hpos offset s)).delete
      (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)) N ⊓
  (stronglyTemperedAtomicAtExponent
    (spectralConeCarrier.delete (productOriginalHeadDeletion s (computedOriginalHeadMask s m))) N).comap
      temperedFourierLinearMap

/-- Fixed common exponent on the two genuine original directed records implies
membership in the COMPLETE original strong pair space. -/
theorem coupledComputedOriginalDirectedExponentLayer_le_strongPair (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m N : ℕ) :
    coupledComputedOriginalDirectedExponentLayer scales hpos offset s hs m N ≤
      CompactOriginal.productOriginalStrongDeletedPairSpace
        (coupledCompactOriginalParameterBlock scales hpos offset s)
        (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
        (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) := by
  intro T hT
  exact ⟨(mem_stronglyTemperedAtomicOnCarrier_iff _ T).mpr ⟨N, hT.1⟩,
    (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mpr ⟨N, hT.2⟩⟩

/-- EVERY complete original fixed-exponent directed layer is zero at N<s. -/
theorem coupledComputedOriginalDirectedExponentLayer_eq_bot_of_lt (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m N : ℕ) (hN : N < s) :
    coupledComputedOriginalDirectedExponentLayer scales hpos offset s hs m N = ⊥ := by
  apply le_antisymm _ bot_le
  intro T hT
  apply (Submodule.mem_bot ℂ).mpr
  by_contra hn
  exact coupledComputedOriginalStrongPair_not_lowExponent scales hpos offset s hs m N hN T
    (coupledComputedOriginalDirectedExponentLayer_le_strongPair scales hpos offset s hs m N hT) hn hT.1

/-- At N≥s+3 the complete original weighted pair layer exhausts the COMPLETE strong line.
The proof admits ALL original supported pairs, retaining both absolute-mass records. -/
theorem coupledComputedOriginalDirectedExponentLayer_eq_strongPair_of_ge (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m N : ℕ) (hN : s + 3 ≤ N) :
    coupledComputedOriginalDirectedExponentLayer scales hpos offset s hs m N =
      CompactOriginal.productOriginalStrongDeletedPairSpace
        (coupledCompactOriginalParameterBlock scales hpos offset s)
        (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
        (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) := by
  apply le_antisymm (coupledComputedOriginalDirectedExponentLayer_le_strongPair scales hpos offset s hs m N)
  intro T hT
  have hpair : T ∈ CompactOriginal.productOriginalDeletedPairSpace
      (coupledCompactOriginalParameterBlock scales hpos offset s)
      (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m)) := by
    rw [← CompactOriginal.productOriginalStrongDeletedPairSpace_eq_pair]
    exact hT
  exact ⟨stronglyTemperedAtomicAtExponent_mono _ (by omega)
    (CompactOriginal.productOriginalDeletedPair_physical_mem_strongExponent _ _ _ ⟨T, hpair⟩),
    stronglyTemperedAtomicAtExponent_mono _ hN
      (CompactOriginal.productOriginalDeletedPair_spectral_mem_strongExponent _ _ _ ⟨T, hpair⟩)⟩

/-- The complete original high-exponent directed layer has EXACT complex dimension one. -/
theorem coupledComputedOriginalDirectedExponentLayer_finrank_one_of_ge (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m N : ℕ) (hN : s + 3 ≤ N) :
    Module.finrank ℂ (coupledComputedOriginalDirectedExponentLayer scales hpos offset s hs m N) = 1 := by
  rw [coupledComputedOriginalDirectedExponentLayer_eq_strongPair_of_ge scales hpos offset s hs m N hN]
  exact (coupledComputedOriginalStrongPair_complete_line scales hpos offset s hs m).1

/-- EVERY complete original directed exponent layer is finite-dimensional, including
the unresolved intermediate orders between s and s+3. -/
theorem coupledComputedOriginalDirectedExponentLayer_finiteDimensional (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m N : ℕ) :
    FiniteDimensional ℂ (coupledComputedOriginalDirectedExponentLayer scales hpos offset s hs m N) := by
  letI : FiniteDimensional ℂ (CompactOriginal.productOriginalStrongDeletedPairSpace
      (coupledCompactOriginalParameterBlock scales hpos offset s)
      (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)
      (productOriginalHeadDeletion s (computedOriginalHeadMask s m))) :=
    FiniteDimensional.of_finrank_pos (by
      rw [(coupledComputedOriginalStrongPair_complete_line scales hpos offset s hs m).1]
      norm_num)
  exact Submodule.finiteDimensional_of_le
    (coupledComputedOriginalDirectedExponentLayer_le_strongPair scales hpos offset s hs m N)

end

end MeyerGeneralProblem.StrongParity
