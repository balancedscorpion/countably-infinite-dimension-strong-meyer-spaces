module

public import MeyerGeneralProblem.UniformDiscrete.OriginalTriangularProjection
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-! A definite free-coordinate basis from an ORIGINAL pivot projection.
Zero padding and the specified projection give both inverse maps. No arbitrary
complement, unknown-rank basis extraction or complex zero test is used. -/

namespace MeyerGeneralProblem.UniformDiscrete

open Module

noncomputable section

/-- Every original coordinate outside the specified original pivot image. -/
abbrev originalFreeIndex {I J : Type*} (pivotIndex : I → J) :=
  {j : J // j ∉ Set.range pivotIndex}

/-- The free coordinate type is finite whenever the whole coordinate type is. -/
instance originalFreeIndex_fintype {I J : Type*} [Fintype J] (pivotIndex : I → J) :
    Fintype (originalFreeIndex pivotIndex) := by
  classical
  unfold originalFreeIndex
  infer_instance

variable {K I J : Type*} [Field K] [Fintype J] [DecidableEq J]

/-- Read the literal original free coordinates. -/
def originalFreeRestrict (pivotIndex : I → J) :
    (J → K) →ₗ[K] (originalFreeIndex pivotIndex → K) where
  toFun v j := v j.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Zero padding in EVERY original pivot coordinate. -/
def originalFreeExtend (pivotIndex : I → J) :
    (originalFreeIndex pivotIndex → K) →ₗ[K] (J → K) := by
  classical
  refine { toFun := fun v j => if h : j ∉ Set.range pivotIndex then v ⟨j, h⟩ else 0
           map_add' := ?_, map_smul' := ?_ }
  · intro v w
    funext j
    change (if h : j ∉ Set.range pivotIndex then (v + w) ⟨j, h⟩ else 0) =
      (if h : j ∉ Set.range pivotIndex then v ⟨j, h⟩ else 0) +
      (if h : j ∉ Set.range pivotIndex then w ⟨j, h⟩ else 0)
    split_ifs <;> first | rfl | simp only [zero_add]
  · intro c v
    funext j
    change (if h : j ∉ Set.range pivotIndex then (c • v) ⟨j, h⟩ else 0) =
      c • (if h : j ∉ Set.range pivotIndex then v ⟨j, h⟩ else 0)
    split_ifs <;> first | rfl | simp only [smul_zero]

omit [Fintype J] [DecidableEq J] in
theorem originalFreeExtend_apply_free (pivotIndex : I → J)
    (v : originalFreeIndex pivotIndex → K) (j : originalFreeIndex pivotIndex) :
    originalFreeExtend pivotIndex v j.val = v j := by
  classical
  change (if h : j.val ∉ Set.range pivotIndex then v ⟨j.val, h⟩ else 0) = v j
  rw [dite_eq_left j.property]

omit [Fintype J] [DecidableEq J] in
theorem originalFreeExtend_apply_pivot (pivotIndex : I → J)
    (v : originalFreeIndex pivotIndex → K) (i : I) :
    originalFreeExtend pivotIndex v (pivotIndex i) = 0 := by
  classical
  change (if h : pivotIndex i ∉ Set.range pivotIndex then v ⟨pivotIndex i, h⟩ else 0) = 0
  rw [dite_eq_right (show ¬pivotIndex i ∉ Set.range pivotIndex from fun h => h ⟨i, rfl⟩)]

omit [Fintype J] in
theorem originalFreeExtend_single (pivotIndex : I → J)
    [DecidableEq (originalFreeIndex pivotIndex)] (j : originalFreeIndex pivotIndex) :
    originalFreeExtend pivotIndex (Pi.single j (1 : K)) = Pi.single j.val 1 := by
  classical
  funext k
  by_cases hk : k ∉ Set.range pivotIndex
  · rw [originalFreeExtend_apply_free pivotIndex _ ⟨k, hk⟩]
    simp only [Pi.single_apply, Subtype.ext_iff]
  · obtain ⟨i, rfl⟩ := not_not.mp hk
    rw [originalFreeExtend_apply_pivot]
    have hne : j.val ≠ pivotIndex i := fun h => j.property ⟨i, h.symm⟩
    simp only [Pi.single_apply, Ne.symm hne, ite_false]

theorem originalProjection_freeExtend_restrict (pivotIndex : I → J)
    (P : (J → K) →ₗ[K] (J → K))
    (hpivot : ∀ i, P (Pi.single (pivotIndex i) 1) = 0) (v : J → K) :
    P (originalFreeExtend pivotIndex (originalFreeRestrict pivotIndex v)) = P v := by
  classical
  have hexp (w : J → K) : w = ∑ j : J, w j • Pi.single j (1 : K) := by
    funext j
    simp [Pi.single_apply]
  calc
    _ = ∑ j : J, originalFreeExtend pivotIndex (originalFreeRestrict pivotIndex v) j •
        P (Pi.single j 1) := by
      exact (congrArg P (hexp _)).trans (by simp only [map_sum, map_smul])
    _ = ∑ j : J, v j • P (Pi.single j 1) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∉ Set.range pivotIndex
      · rw [originalFreeExtend_apply_free pivotIndex _ ⟨j, hj⟩]
        rfl
      · obtain ⟨i, rfl⟩ := not_not.mp hj
        rw [hpivot i, smul_zero, smul_zero]
    _ = P v := by
      exact ((congrArg P (hexp v)).trans (by simp only [map_sum, map_smul])).symm

/-- The WHOLE original row kernel is identified with its ORIGINAL free
coordinates by the definite specified projection and zero padding. -/
def originalFreeKernelEquiv (row : I → (J → K) →ₗ[K] K) (pivotIndex : I → J)
    (P : (J → K) →ₗ[K] (J → K))
    (hrow : ∀ v, P v ∈ rowKernel row)
    (hfix : ∀ v ∈ rowKernel row, P v = v)
    (hpivot : ∀ i, P (Pi.single (pivotIndex i) 1) = 0)
    (hfree : ∀ v (j : originalFreeIndex pivotIndex), P v j.val = v j.val) :
    rowKernel row ≃ₗ[K] (originalFreeIndex pivotIndex → K) where
  __ := (originalFreeRestrict pivotIndex).comp (rowKernel row).subtype
  invFun v := ⟨P (originalFreeExtend pivotIndex v), hrow _⟩
  left_inv v := by
    apply Subtype.ext
    change P (originalFreeExtend pivotIndex (originalFreeRestrict pivotIndex v.val)) = v.val
    rw [originalProjection_freeExtend_restrict pivotIndex P hpivot, hfix _ v.property]
  right_inv v := by
    funext j
    change P (originalFreeExtend pivotIndex v) j.val = v j
    rw [hfree, originalFreeExtend_apply_free]

/-- The standard free-coordinate basis transported by the literal ORIGINAL
projection, rather than a chosen basis of an unspecified complement. -/
def originalFreeKernelBasis (row : I → (J → K) →ₗ[K] K) (pivotIndex : I → J)
    (P : (J → K) →ₗ[K] (J → K))
    (hrow : ∀ v, P v ∈ rowKernel row)
    (hfix : ∀ v ∈ rowKernel row, P v = v)
    (hpivot : ∀ i, P (Pi.single (pivotIndex i) 1) = 0)
    (hfree : ∀ v (j : originalFreeIndex pivotIndex), P v j.val = v j.val) :
    Basis (originalFreeIndex pivotIndex) K (rowKernel row) :=
  (Pi.basisFun K (originalFreeIndex pivotIndex)).map
    (originalFreeKernelEquiv row pivotIndex P hrow hfix hpivot hfree).symm

theorem originalFreeKernelBasis_vector (row : I → (J → K) →ₗ[K] K) (pivotIndex : I → J)
    (P : (J → K) →ₗ[K] (J → K))
    (hrow : ∀ v, P v ∈ rowKernel row) (hfix : ∀ v ∈ rowKernel row, P v = v)
    (hpivot : ∀ i, P (Pi.single (pivotIndex i) 1) = 0)
    (hfree : ∀ v (j : originalFreeIndex pivotIndex), P v j.val = v j.val)
    (j : originalFreeIndex pivotIndex) :
    (originalFreeKernelBasis row pivotIndex P hrow hfix hpivot hfree j : J → K) =
      P (Pi.single j.val 1) := by
  classical
  rw [originalFreeKernelBasis, Basis.map_apply, Pi.basisFun_apply]
  change P (originalFreeExtend pivotIndex (Pi.single j 1)) = _
  rw [originalFreeExtend_single]

end

end MeyerGeneralProblem.UniformDiscrete
