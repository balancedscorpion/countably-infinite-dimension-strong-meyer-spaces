module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadRank
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductDeletedPairs
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductGapLine
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductOriginalRows
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadGapBasis

@[expose] public section

/-! Complete original OriginalHeadGapBasis for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The COMPLETE original retained head kernel with literal corner value zero. -/
def productOriginalHeadCornerKernel {s : ℕ} (block : CompactOriginalParameterBlock s) (A : Finset (productOriginalHeadLabel s)) :
    Submodule ℂ (productOriginalHeadKernel block A) :=
  LinearMap.ker ((productCornerFunctional s).comp (productOriginalHeadKernel block A).subtype)

/-- Every ORIGINAL physical root evaluation on the whole original head/corner kernel. -/
def productOriginalHeadCornerPhysicalRow {s : ℕ} (block : CompactOriginalParameterBlock s) (A : Finset (productOriginalHeadLabel s))
    (x : (compactOriginalProductSheetCarrier block).subtype) : productOriginalHeadCornerKernel block A →ₗ[ℂ] ℂ :=
  (productOriginalPhysicalRow block x).comp ((productOriginalHeadKernel block A).subtype.comp
    (productOriginalHeadCornerKernel block A).subtype)

theorem productOriginalHeadCornerPhysicalRows_separate {s : ℕ} (block : CompactOriginalParameterBlock s)
    (A : Finset (productOriginalHeadLabel s)) :
    ∀ v : productOriginalHeadCornerKernel block A,
      (∀ x, productOriginalHeadCornerPhysicalRow block A x v = 0) → v = 0 := by
  intro v hv
  have hh : (v.val : productNumeratorIndex s → ℂ) = 0 :=
    productOriginalPhysicalRows_separate block _ hv
  apply Subtype.ext
  apply Subtype.ext
  change (v.val : productNumeratorIndex s → ℂ) = 0
  exact hh

/-- On ANY specified finite basis of the actual head/corner kernel there is
a nonzero determinant of exactly the required number of ORIGINAL root rows.
This is the algebraic search-existence input, without an effective analytic oracle. -/
theorem productOriginalHeadCorner_original_det_ne_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) {J : Type*} [Fintype J] [DecidableEq J]
    (b : Module.Basis J ℂ (productOriginalHeadCornerKernel block A)) :
    ∃ E : Finset (compactOriginalProductSheetCarrier block).subtype, ∃ e : E ≃ J,
      E.card + A.card + 2 = (s + 1) ^ 2 ∧
      Matrix.det (fun i j : J =>
        productOriginalHeadCornerPhysicalRow block A (e.symm i) (b j)) ≠ 0 := by
  obtain ⟨E, e, hcard, hdet⟩ := UniformDiscrete.exists_original_evaluation_det_ne_zero
    (K := ℂ) (V := productOriginalHeadCornerKernel block A) (J := J)
    (productOriginalHeadCornerPhysicalRow block A)
    (productOriginalHeadCornerPhysicalRows_separate block A) b
  refine ⟨E, e, ?_, hdet⟩
  have hH := productOriginalHeadKernel_finrank_add_card block hs A
  have hW := productOriginalHeadKernel_corner_kernel_finrank_add_one block hs A
  change Module.finrank ℂ (productOriginalHeadCornerKernel block A) + 1 =
    Module.finrank ℂ (productOriginalHeadKernel block A) at hW
  have hbox : 1 ≤ (s + 1) ^ 2 := by nlinarith
  omega

/-- Exactly the required number of ORIGINAL root deletions leave one complete
strong pair line, with all original retained head coefficients zero and
the actual corner value normalized to one. -/
theorem productOriginalHeadGapLine_exact_card {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    ∃ E : Finset (compactOriginalProductSheetCarrier block).subtype,
      ∃ r : productNumeratorIndex s → ℂ,
        E.card + A.card + 2 = (s + 1) ^ 2 ∧
        Module.finrank ℂ (productOriginalStrongDeletedPairSpace block
          (productSelectedPhysicalDeletion block E) (productOriginalHeadDeletion s A)) = 1 ∧
        r ∈ productOriginalDeletionKernel block (productSelectedPhysicalDeletion block E)
          (productOriginalHeadDeletion s A) ∧
        productCornerFunctional s r = 1 := by
  obtain ⟨E, hcard, hdim, v, hv, hj⟩ :=
    UniformDiscrete.exists_compatible_selected_line_exact_card
      (productOriginalPhysicalRow block) (productOriginalPhysicalRows_separate block)
      (productOriginalHeadKernel block A) (productCornerFunctional s)
      ⟨productMiddleMonomial s hs, productMiddleMonomial_mem_originalHeadKernel block hs A,
        by rw [productMiddleMonomial_corner]; exact one_ne_zero⟩
  have hvK : v ∈ productOriginalDeletionKernel block (productSelectedPhysicalDeletion block E)
      (productOriginalHeadDeletion s A) := by
    rw [productOriginalDeletionKernel_selectedPhysical,
      ← productOriginalHeadKernel_eq_deletionKernel]
    exact hv
  refine ⟨E, (productCornerFunctional s v)⁻¹ • v, ?_, ?_, ?_, ?_⟩
  · have hH := productOriginalHeadKernel_finrank_add_card block hs A
    have hbox : 1 ≤ (s + 1) ^ 2 := by nlinarith
    omega
  · rw [productOriginalStrongDeletedPairSpace_finrank_eq_kernel,
      productOriginalDeletionKernel_selectedPhysical,
      ← productOriginalHeadKernel_eq_deletionKernel]
    exact hdim
  · exact (productOriginalDeletionKernel block (productSelectedPhysicalDeletion block E)
      (productOriginalHeadDeletion s A)).smul_mem _ hvK
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hj]

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
