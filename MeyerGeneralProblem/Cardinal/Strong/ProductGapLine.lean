module

public import MeyerGeneralProblem.Cardinal.Strong.ProductMiddleGap
public import MeyerGeneralProblem.Cardinal.Strong.ProductDeletedPairs
public import MeyerGeneralProblem.UniformDiscrete.CompatibleFiniteRows
public import MeyerGeneralProblem.Cardinal.Strong.ReturnMassGrowth

@[expose] public section

/-! Compatible selection of ORIGINAL root evaluations on the complete
original spectral head kernel. The resulting two-carrier space is exactly
one strong line and has an actual normalized numerator with `R(1,1)=1`.
This finite choice does not assert the later infinite common-carrier exhaustion. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The actual real points of the selected ORIGINAL roots, with no proxy rows. -/
def productSelectedPhysicalDeletion (s : ℕ) (E : Finset (productSheetCarrier s).subtype) :
    Set ℝ := Subtype.val '' (E : Set (productSheetCarrier s).subtype)

theorem productSelectedPhysicalDeletion_finite (s : ℕ)
    (E : Finset (productSheetCarrier s).subtype) :
    (productSelectedPhysicalDeletion s E).Finite := E.finite_toSet.image Subtype.val

theorem productOriginalDeletionKernel_selectedPhysical (s : ℕ)
    (E : Finset (productSheetCarrier s).subtype) (F : Set ℝ) :
    productOriginalDeletionKernel s (productSelectedPhysicalDeletion s E) F =
      productOriginalDeletionKernel s ∅ F ⊓
        LinearMap.ker (UniformDiscrete.selectedRowMap (productOriginalPhysicalRow s) E) := by
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
theorem productOriginalGapLine_exists (s : ℕ) (hs : 2 ≤ s) (F : Set ℝ)
    (hF : ∀ x ∈ F, |x| ≤ ((s / 2 : ℕ) : ℝ) / 2) :
    ∃ E : Finset (productSheetCarrier s).subtype,
      ∃ r : productNumeratorIndex s → ℂ,
        Module.finrank ℂ (productOriginalStrongDeletedPairSpace s
          (productSelectedPhysicalDeletion s E) F) = 1 ∧
        r ∈ productOriginalDeletionKernel s (productSelectedPhysicalDeletion s E) F ∧
        productCornerFunctional s r = 1 := by
  obtain ⟨E, hdim, v, hv, hj⟩ := UniformDiscrete.exists_compatible_selected_line
    (productOriginalPhysicalRow s) (productOriginalPhysicalRows_separate s)
    (productOriginalDeletionKernel s ∅ F) (productCornerFunctional s)
    ⟨productMiddleMonomial s hs, productMiddleMonomial_mem_original_head_kernel s hs F hF,
      by rw [productMiddleMonomial_corner]; exact one_ne_zero⟩
  have hvK : v ∈ productOriginalDeletionKernel s (productSelectedPhysicalDeletion s E) F := by
    rw [productOriginalDeletionKernel_selectedPhysical]
    exact hv
  refine ⟨E, (productCornerFunctional s v)⁻¹ • v, ?_, ?_, ?_⟩
  · rw [productOriginalStrongDeletedPairSpace_finrank_eq_kernel,
      productOriginalDeletionKernel_selectedPhysical]
    exact hdim
  · exact (productOriginalDeletionKernel s (productSelectedPhysicalDeletion s E) F).smul_mem _ hvK
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hj]

/-- The full actual deleted pair space is spanned by a normalized original
source. This characterizes ARBITRARY original distributions, not just a map's image. -/
theorem productOriginalGapLine_complete_span (s : ℕ) (E F : Set ℝ)
    (r : productNumeratorIndex s → ℂ)
    (hdim : Module.finrank ℂ (productOriginalDeletionKernel s E F) = 1)
    (hr : r ∈ productOriginalDeletionKernel s E F) (hj : productCornerFunctional s r = 1) :
    ∀ T : TemperedDistribution ℝ ℂ,
      T ∈ productOriginalDeletedPairSpace s E F ↔
        ∃ c : ℂ, T = c • productPhysicalDistribution s r := by
  have hr0 : r ≠ 0 := by
    intro hz
    have hh : (0 : ℂ) = 1 := by simpa only [hz, map_zero] using hj
    exact zero_ne_one hh
  have hK : productOriginalDeletionKernel s E F = Submodule.span ℂ {r} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hr hr0
  intro T
  constructor
  · intro hT
    obtain ⟨u, hu⟩ := (productOriginalDeletedPairConstructionMap_bijective s E F).2 ⟨T, hT⟩
    have humem : (u : productNumeratorIndex s → ℂ) ∈ Submodule.span ℂ {r} :=
      hK ▸ u.property
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp humem
    refine ⟨c, ?_⟩
    have hTu : productPhysicalDistribution s u = T := congrArg Subtype.val hu
    rw [← hTu, ← hc, productPhysicalDistribution_smul]
  · rintro ⟨c, rfl⟩
    exact (productOriginalDeletedPairSpace s E F).smul_mem c
      ((productPhysical_mem_deletedPairSpace_iff s E F r).mpr hr)

/-- Original low-exponent exclusion survives the actual root deletions.
There is no change to the weighted record or cancellation proxy. -/
theorem productOriginalGapLine_not_strongExponent (s : ℕ) (i : Fin s)
    (E : Set ℝ) (r : productNumeratorIndex s → ℂ)
    (hj : productCornerFunctional s r ≠ 0) (N : ℕ) (hN : N ≤ s - 1) :
    productPhysicalDistribution s r ∉
      stronglyTemperedAtomicAtExponent ((productSheetCarrier s).delete E) N := by
  intro h
  apply productPhysicalDistribution_not_strongExponent s i r hj N hN
  exact stronglyTemperedAtomicAtExponent_mono_carrier Set.sdiff_subset N _ h

end

end MeyerGeneralProblem.StrongParity
