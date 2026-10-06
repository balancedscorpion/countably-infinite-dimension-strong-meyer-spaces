module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadTriangular
public import MeyerGeneralProblem.Cardinal.Strong.ProductMiddleGap
public import MeyerGeneralProblem.Cardinal.Strong.ProductDeletedPairs
public import MeyerGeneralProblem.UniformDiscrete.IndependentRowRank

@[expose] public section

/-! Exact full original head-kernel ranks, retaining ANY chosen head subset.
Both quarter-phased signs and the unique zero label are part of the original
row family. The corner restriction has exact codimension one. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Every retained original head row, rather than an arbitrary kernel proxy. -/
def productOriginalRetainedHeadRow (s : ℕ) (A : Finset (productOriginalHeadLabel s))
    (p : A) : (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ := productOriginalHeadRow s p.val

/-- The simultaneous kernel of the entire retained ORIGINAL head family. -/
def productOriginalHeadKernel (s : ℕ) (A : Finset (productOriginalHeadLabel s)) :
    Submodule ℂ (productNumeratorIndex s → ℂ) :=
  UniformDiscrete.rowKernel (productOriginalRetainedHeadRow s A)

/-- The actual real Fourier points of EVERY retained original head row. -/
def productOriginalHeadDeletion (s : ℕ) (A : Finset (productOriginalHeadLabel s)) : Set ℝ :=
  (fun p : productOriginalHeadLabel s => spectralConeIndexFrequency p.val) ''
    (A : Set (productOriginalHeadLabel s))

theorem productOriginalHeadKernel_eq_deletionKernel (s : ℕ)
    (A : Finset (productOriginalHeadLabel s)) :
    productOriginalHeadKernel s A =
      productOriginalDeletionKernel s ∅ (productOriginalHeadDeletion s A) := by
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

theorem productOriginalRetainedHeadRows_linearIndependent (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    LinearIndependent ℂ (productOriginalRetainedHeadRow s A) :=
  (productOriginalHeadRows_linearIndependent s hs).comp _ Subtype.val_injective

theorem productOriginalHeadKernel_finrank_add_card (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.finrank ℂ (productOriginalHeadKernel s A) + A.card = (s + 1) ^ 2 - 1 := by
  have h := UniformDiscrete.finrank_rowKernel_add_card_of_linearIndependent
    (productOriginalRetainedHeadRow s A) (productOriginalRetainedHeadRows_linearIndependent s hs A)
  convert! h using 1
  · simp only [Fintype.card_coe]
    rfl
  · simp only [Module.finrank_fintype_fun_eq_card, productNumeratorIndex_card]

theorem productOriginalHeadKernel_finrank (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.finrank ℂ (productOriginalHeadKernel s A) = (s + 1) ^ 2 - 1 - A.card := by
  have h := productOriginalHeadKernel_finrank_add_card s hs A
  omega

/-- Exact dimension of the COMPLETE actual strong directed pair space after
these ORIGINAL spectral deletions, with arbitrary original pairs quantified. -/
theorem productOriginalStrongHeadPairSpace_finrank (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.finrank ℂ (productOriginalStrongDeletedPairSpace s ∅
      (productOriginalHeadDeletion s A)) = (s + 1) ^ 2 - 1 - A.card := by
  rw [productOriginalStrongDeletedPairSpace_finrank_eq_kernel,
    ← productOriginalHeadKernel_eq_deletionKernel]
  exact productOriginalHeadKernel_finrank s hs A

theorem productMiddleMonomial_mem_originalHeadKernel (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    productMiddleMonomial s hs ∈ productOriginalHeadKernel s A := by
  intro p
  exact productMiddleMonomial_original_head_zero s hs (spectralConeIndexPoint p.val.val)
    p.val.property

theorem productOriginalHeadKernel_corner_ne_zero (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    (productCornerFunctional s).comp (productOriginalHeadKernel s A).subtype ≠ 0 := by
  intro h
  have heq := LinearMap.congr_fun h
    ⟨productMiddleMonomial s hs, productMiddleMonomial_mem_originalHeadKernel s hs A⟩
  have hh : (1 : ℂ) = 0 := by simpa only [LinearMap.comp_apply,
    Submodule.subtype_apply, productMiddleMonomial_corner, LinearMap.zero_apply] using heq
  exact one_ne_zero hh

theorem productOriginalHeadKernel_corner_kernel_finrank_add_one (s : ℕ) (hs : 2 ≤ s)
    (A : Finset (productOriginalHeadLabel s)) :
    Module.finrank ℂ (LinearMap.ker ((productCornerFunctional s).comp
      (productOriginalHeadKernel s A).subtype)) + 1 =
        Module.finrank ℂ (productOriginalHeadKernel s A) :=
  Module.Dual.finrank_ker_add_one_of_ne_zero (productOriginalHeadKernel_corner_ne_zero s hs A)

end

end MeyerGeneralProblem.StrongParity
