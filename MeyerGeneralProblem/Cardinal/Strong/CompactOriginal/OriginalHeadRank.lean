module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadLabels
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadTriangular
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductDeletedPairs
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductMiddleGap
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductOriginalRows
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadRank

@[expose] public section

/-! Complete original OriginalHeadRank for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- Every retained original head row, rather than an arbitrary kernel proxy. -/
def productOriginalRetainedHeadRow {s : ℕ} (block : CompactOriginalParameterBlock s) (A : Finset (productOriginalHeadLabel s))
    (p : A) : (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ := productOriginalHeadRow block p.val

/-- The simultaneous kernel of the entire retained ORIGINAL head family. -/
def productOriginalHeadKernel {s : ℕ} (block : CompactOriginalParameterBlock s) (A : Finset (productOriginalHeadLabel s)) :
    Submodule ℂ (productNumeratorIndex s → ℂ) :=
  UniformDiscrete.rowKernel (productOriginalRetainedHeadRow block A)

theorem productOriginalHeadKernel_eq_deletionKernel {s : ℕ} (block : CompactOriginalParameterBlock s)
    (A : Finset (productOriginalHeadLabel s)) :
    productOriginalHeadKernel block A =
      productOriginalDeletionKernel block ∅ (productOriginalHeadDeletion s A) := by
  ext r
  rw [mem_productOriginalDeletionKernel_iff]
  constructor
  · intro h
    refine ⟨by simp, ?_⟩
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hx
    have heq : spectralConeIndexPoint p.val = x := Subtype.ext hpx
    rw [← heq]
    exact h ⟨p, hp⟩
  · rintro ⟨_, h⟩ p
    apply h
    exact ⟨p.val, p.property, rfl⟩

theorem productOriginalRetainedHeadRows_linearIndependent {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    LinearIndependent ℂ (productOriginalRetainedHeadRow block A) :=
  (productOriginalHeadRows_linearIndependent block hs).comp _ Subtype.val_injective

theorem productOriginalHeadKernel_finrank_add_card {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.finrank ℂ (productOriginalHeadKernel block A) + A.card = (s + 1) ^ 2 - 1 := by
  have h := UniformDiscrete.finrank_rowKernel_add_card_of_linearIndependent
    (productOriginalRetainedHeadRow block A) (productOriginalRetainedHeadRows_linearIndependent block hs A)
  convert! h using 1
  · simp only [Fintype.card_coe]
    rfl
  · simp only [Module.finrank_fintype_fun_eq_card, productNumeratorIndex_card]

theorem productOriginalHeadKernel_finrank {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.finrank ℂ (productOriginalHeadKernel block A) = (s + 1) ^ 2 - 1 - A.card := by
  have h := productOriginalHeadKernel_finrank_add_card block hs A
  omega

/-- Exact dimension of the COMPLETE actual strong directed pair space after
these ORIGINAL spectral deletions, with arbitrary original pairs quantified. -/
theorem productOriginalStrongHeadPairSpace_finrank {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.finrank ℂ (productOriginalStrongDeletedPairSpace block ∅
      (productOriginalHeadDeletion s A)) = (s + 1) ^ 2 - 1 - A.card := by
  rw [productOriginalStrongDeletedPairSpace_finrank_eq_kernel,
    ← productOriginalHeadKernel_eq_deletionKernel]
  exact productOriginalHeadKernel_finrank block hs A

theorem productMiddleMonomial_mem_originalHeadKernel {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    productMiddleMonomial s hs ∈ productOriginalHeadKernel block A := by
  intro p
  exact productMiddleMonomial_original_head_zero block hs (spectralConeIndexPoint p.val.val)
    p.val.property

theorem productOriginalHeadKernel_corner_ne_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    (productCornerFunctional s).comp (productOriginalHeadKernel block A).subtype ≠ 0 := by
  intro h
  have heq := LinearMap.congr_fun h
    ⟨productMiddleMonomial s hs, productMiddleMonomial_mem_originalHeadKernel block hs A⟩
  have hh : (1 : ℂ) = 0 := by simpa only [LinearMap.comp_apply,
    Submodule.subtype_apply, productMiddleMonomial_corner, LinearMap.zero_apply] using heq
  exact one_ne_zero hh

theorem productOriginalHeadKernel_corner_kernel_finrank_add_one {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.finrank ℂ (LinearMap.ker ((productCornerFunctional s).comp
      (productOriginalHeadKernel block A).subtype)) + 1 =
        Module.finrank ℂ (productOriginalHeadKernel block A) :=
  Module.Dual.finrank_ker_add_one_of_ne_zero (productOriginalHeadKernel_corner_ne_zero block hs A)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
