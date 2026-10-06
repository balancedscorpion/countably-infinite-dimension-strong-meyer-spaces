module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.PhysicalDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductDeletedPairs
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductMiddleGap
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductOriginalRows
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ReturnMassGrowth
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductGapLine

@[expose] public section

/-! Complete original ProductGapLine for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The actual real points of the selected ORIGINAL roots, with no proxy rows. -/
def productSelectedPhysicalDeletion {s : ℕ} (block : CompactOriginalParameterBlock s) (E : Finset (compactOriginalProductSheetCarrier block).subtype) :
    Set ℝ := Subtype.val '' (E : Set (compactOriginalProductSheetCarrier block).subtype)

theorem productSelectedPhysicalDeletion_finite {s : ℕ} (block : CompactOriginalParameterBlock s)
    (E : Finset (compactOriginalProductSheetCarrier block).subtype) :
    (productSelectedPhysicalDeletion block E).Finite := E.finite_toSet.image Subtype.val

theorem productOriginalDeletionKernel_selectedPhysical {s : ℕ} (block : CompactOriginalParameterBlock s)
    (E : Finset (compactOriginalProductSheetCarrier block).subtype) (F : Set ℝ) :
    productOriginalDeletionKernel block (productSelectedPhysicalDeletion block E) F =
      productOriginalDeletionKernel block ∅ F ⊓
        LinearMap.ker (UniformDiscrete.selectedRowMap (productOriginalPhysicalRow block) E) := by
  ext r
  rw [mem_productOriginalDeletionKernel_iff, Submodule.mem_inf,
    mem_productOriginalDeletionKernel_iff, UniformDiscrete.mem_ker_selectedRowMap]
  constructor
  · rintro ⟨hE, hF⟩
    refine ⟨⟨by simp, hF⟩, fun x hx => hE x ?_⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨⟨_, hF⟩, hE⟩
    refine ⟨?_, hF⟩
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    have heq : y = x := Subtype.ext hyx
    exact heq ▸ hE y hy

/-- For ANY original forbidden spectral set in the actual central head,
finitely many actual root deletions cut the COMPLETE strong pair space to
one line, with the literal original corner value normalized to one. -/
theorem productOriginalGapLine_exists {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s) (F : Set ℝ)
    (hF : ∀ x ∈ F, |x| ≤ ((s / 2 : ℕ) : ℝ) / 2) :
    ∃ E : Finset (compactOriginalProductSheetCarrier block).subtype,
      ∃ r : productNumeratorIndex s → ℂ,
        Module.finrank ℂ (productOriginalStrongDeletedPairSpace block
          (productSelectedPhysicalDeletion block E) F) = 1 ∧
        r ∈ productOriginalDeletionKernel block (productSelectedPhysicalDeletion block E) F ∧
        productCornerFunctional s r = 1 := by
  obtain ⟨E, hdim, v, hv, hj⟩ := UniformDiscrete.exists_compatible_selected_line
    (productOriginalPhysicalRow block) (productOriginalPhysicalRows_separate block)
    (productOriginalDeletionKernel block ∅ F) (productCornerFunctional s)
    ⟨productMiddleMonomial s hs, productMiddleMonomial_mem_original_head_kernel block hs F hF,
      by rw [productMiddleMonomial_corner]; exact one_ne_zero⟩
  have hvK : v ∈ productOriginalDeletionKernel block (productSelectedPhysicalDeletion block E) F := by
    rw [productOriginalDeletionKernel_selectedPhysical]
    exact hv
  refine ⟨E, (productCornerFunctional s v)⁻¹ • v, ?_, ?_, ?_⟩
  · rw [productOriginalStrongDeletedPairSpace_finrank_eq_kernel,
      productOriginalDeletionKernel_selectedPhysical]
    exact hdim
  · exact (productOriginalDeletionKernel block (productSelectedPhysicalDeletion block E) F).smul_mem _ hvK
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hj]

/-- The full actual deleted pair space is spanned by a normalized original
source. This characterizes ARBITRARY original distributions, not just a map's image. -/
theorem productOriginalGapLine_complete_span {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ)
    (r : productNumeratorIndex s → ℂ)
    (hdim : Module.finrank ℂ (productOriginalDeletionKernel block E F) = 1)
    (hr : r ∈ productOriginalDeletionKernel block E F) (hj : productCornerFunctional s r = 1) :
    ∀ T : TemperedDistribution ℝ ℂ,
      T ∈ productOriginalDeletedPairSpace block E F ↔
        ∃ c : ℂ, T = c • productPhysicalDistribution block r := by
  have hr0 : r ≠ 0 := by
    intro hz
    have hh : (0 : ℂ) = 1 := by simpa only [hz, map_zero] using hj
    exact zero_ne_one hh
  have hK : productOriginalDeletionKernel block E F = Submodule.span ℂ {r} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hr hr0
  intro T
  constructor
  · intro hT
    obtain ⟨u, hu⟩ := (productOriginalDeletedPairConstructionMap_bijective block E F).2 ⟨T, hT⟩
    have humem : (u : productNumeratorIndex s → ℂ) ∈ Submodule.span ℂ {r} :=
      hK ▸ u.property
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp humem
    refine ⟨c, ?_⟩
    have hTu : productPhysicalDistribution block u = T := congrArg Subtype.val hu
    rw [← hTu, ← hc, productPhysicalDistribution_smul]
  · rintro ⟨c, rfl⟩
    exact (productOriginalDeletedPairSpace block E F).smul_mem c
      ((productPhysical_mem_deletedPairSpace_iff block E F r).mpr hr)

/-- Original low-exponent exclusion survives the actual root deletions.
There is no change to the weighted record or cancellation proxy. -/
theorem productOriginalGapLine_not_strongExponent {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s)
    (E : Set ℝ) (r : productNumeratorIndex s → ℂ)
    (hj : productCornerFunctional s r ≠ 0) (N : ℕ) (hN : N ≤ s - 1) :
    productPhysicalDistribution block r ∉
      stronglyTemperedAtomicAtExponent ((compactOriginalProductSheetCarrier block).delete E) N := by
  intro h
  apply productPhysicalDistribution_not_strongExponent block i r hj N hN
  exact stronglyTemperedAtomicAtExponent_mono_carrier Set.sdiff_subset N _ h

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
