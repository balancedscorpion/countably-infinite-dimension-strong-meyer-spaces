module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadRank
public import MeyerGeneralProblem.Cardinal.Strong.ProductGapLine
public import MeyerGeneralProblem.UniformDiscrete.OriginalRowBasisSelection

@[expose] public section

/-! Original root selection with the proved exact deletion count, on ANY
retained subset of the complete signed head. The resulting COMPLETE strong
directed pair space is one line and its original numerator has corner one.
This finite native block does not assert the final common-carrier exhaustion. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The COMPLETE original retained head kernel with literal corner value zero. -/
def productOriginalHeadCornerKernel (s : ℕ) (A : Finset (productOriginalHeadLabel s)) :
    Submodule ℂ (productOriginalHeadKernel s A) :=
  LinearMap.ker ((productCornerFunctional s).comp (productOriginalHeadKernel s A).subtype)

/-- Every ORIGINAL physical root evaluation on the whole original head/corner kernel. -/
def productOriginalHeadCornerPhysicalRow (s : ℕ) (A : Finset (productOriginalHeadLabel s))
    (x : (productSheetCarrier s).subtype) : productOriginalHeadCornerKernel s A →ₗ[ℂ] ℂ :=
  (productOriginalPhysicalRow s x).comp ((productOriginalHeadKernel s A).subtype.comp
    (productOriginalHeadCornerKernel s A).subtype)

theorem productOriginalHeadCornerPhysicalRows_separate (s : ℕ)
    (A : Finset (productOriginalHeadLabel s)) :
    ∀ v : productOriginalHeadCornerKernel s A,
      (∀ x, productOriginalHeadCornerPhysicalRow s A x v = 0) → v = 0 := by
  intro v hv
  have hh : (v.val : productNumeratorIndex s → ℂ) = 0 :=
    productOriginalPhysicalRows_separate s _ hv
  apply Subtype.ext
  apply Subtype.ext
  change (v.val : productNumeratorIndex s → ℂ) = 0
  exact hh

/-- On ANY specified finite basis of the actual head/corner kernel there is
a nonzero determinant of exactly the required number of ORIGINAL root rows.
This is the algebraic search-existence input, without an effective analytic oracle. -/
theorem productOriginalHeadCorner_original_det_ne_zero (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) {J : Type*} [Fintype J] [DecidableEq J]
    (b : Module.Basis J ℂ (productOriginalHeadCornerKernel s A)) :
    ∃ E : Finset (productSheetCarrier s).subtype, ∃ e : E ≃ J,
      E.card + A.card + 2 = (s + 1) ^ 2 ∧
      Matrix.det (fun i j : J =>
        productOriginalHeadCornerPhysicalRow s A (e.symm i) (b j)) ≠ 0 := by
  obtain ⟨E, e, hcard, hdet⟩ := UniformDiscrete.exists_original_evaluation_det_ne_zero
    (K := ℂ) (V := productOriginalHeadCornerKernel s A) (J := J)
    (productOriginalHeadCornerPhysicalRow s A)
    (productOriginalHeadCornerPhysicalRows_separate s A) b
  refine ⟨E, e, ?_, hdet⟩
  have hH := productOriginalHeadKernel_finrank_add_card s hs A
  have hW := productOriginalHeadKernel_corner_kernel_finrank_add_one s hs A
  change Module.finrank ℂ (productOriginalHeadCornerKernel s A) + 1 =
    Module.finrank ℂ (productOriginalHeadKernel s A) at hW
  have hbox : 1 ≤ (s + 1) ^ 2 := by nlinarith
  omega

/-- Exactly the required number of ORIGINAL root deletions leave one complete
strong pair line, with all original retained head coefficients zero and
the actual corner value normalized to one. -/
theorem productOriginalHeadGapLine_exact_card (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    ∃ E : Finset (productSheetCarrier s).subtype,
      ∃ r : productNumeratorIndex s → ℂ,
        E.card + A.card + 2 = (s + 1) ^ 2 ∧
        Module.finrank ℂ (productOriginalStrongDeletedPairSpace s
          (productSelectedPhysicalDeletion s E) (productOriginalHeadDeletion s A)) = 1 ∧
        r ∈ productOriginalDeletionKernel s (productSelectedPhysicalDeletion s E)
          (productOriginalHeadDeletion s A) ∧
        productCornerFunctional s r = 1 := by
  obtain ⟨E, hcard, hdim, v, hv, hj⟩ :=
    UniformDiscrete.exists_compatible_selected_line_exact_card
      (productOriginalPhysicalRow s) (productOriginalPhysicalRows_separate s)
      (productOriginalHeadKernel s A) (productCornerFunctional s)
      ⟨productMiddleMonomial s hs, productMiddleMonomial_mem_originalHeadKernel s hs A,
        by rw [productMiddleMonomial_corner]; exact one_ne_zero⟩
  have hvK : v ∈ productOriginalDeletionKernel s (productSelectedPhysicalDeletion s E)
      (productOriginalHeadDeletion s A) := by
    rw [productOriginalDeletionKernel_selectedPhysical,
      ← productOriginalHeadKernel_eq_deletionKernel]
    exact hv
  refine ⟨E, (productCornerFunctional s v)⁻¹ • v, ?_, ?_, ?_, ?_⟩
  · have hH := productOriginalHeadKernel_finrank_add_card s hs A
    have hbox : 1 ≤ (s + 1) ^ 2 := by nlinarith
    omega
  · rw [productOriginalStrongDeletedPairSpace_finrank_eq_kernel,
      productOriginalDeletionKernel_selectedPhysical,
      ← productOriginalHeadKernel_eq_deletionKernel]
    exact hdim
  · exact (productOriginalDeletionKernel s (productSelectedPhysicalDeletion s E)
      (productOriginalHeadDeletion s A)).smul_mem _ hvK
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hj]

end

end MeyerGeneralProblem.StrongParity
