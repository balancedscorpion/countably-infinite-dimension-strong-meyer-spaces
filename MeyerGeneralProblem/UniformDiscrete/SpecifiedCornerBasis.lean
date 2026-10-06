module

public import MeyerGeneralProblem.UniformDiscrete.OriginalFreeKernelBasis

@[expose] public section

/-! A definite corner-zero basis from a SPECIFIED finite basis and a
specified basis vector of corner one. Every other vector is corrected by
its literal corner multiple; no arbitrary complement or rank test occurs. -/

namespace MeyerGeneralProblem.UniformDiscrete

open Module

noncomputable section

variable {K V J : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype J] [DecidableEq J]

theorem specifiedBasis_inverse_single (b : Basis J K V) (j : J) :
    b.equivFun.symm (Pi.single j 1) = b j := by
  simp [Basis.equivFun_symm_apply, Pi.single_apply]

/-- The actual specified functional in the given finite basis coordinates. -/
def specifiedCornerCoordinateFunctional (b : Basis J K V) (L : V →ₗ[K] K) :
    (J → K) →ₗ[K] K := L.comp b.equivFun.symm.toLinearMap

/-- Subtract the literal corner multiple of the specified anchor coordinate. -/
def specifiedCornerCoordinateProjection (b : Basis J K V) (L : V →ₗ[K] K) (j₀ : J) :
    (J → K) →ₗ[K] (J → K) :=
  LinearMap.id - (specifiedCornerCoordinateFunctional b L).smulRight (Pi.single j₀ 1)

theorem specifiedCornerCoordinateProjection_apply (b : Basis J K V) (L : V →ₗ[K] K)
    (j₀ : J) (v : J → K) :
    specifiedCornerCoordinateProjection b L j₀ v =
      v - specifiedCornerCoordinateFunctional b L v • Pi.single j₀ 1 := rfl

theorem specifiedCornerCoordinateFunctional_single (b : Basis J K V) (L : V →ₗ[K] K)
    (j : J) : specifiedCornerCoordinateFunctional b L (Pi.single j 1) = L (b j) := by
  change L (b.equivFun.symm (Pi.single j 1)) = _
  rw [specifiedBasis_inverse_single]

theorem specifiedCornerCoordinateProjection_mem_kernel (b : Basis J K V) (L : V →ₗ[K] K)
    (j₀ : J) (h₀ : L (b j₀) = 1) (v : J → K) :
    specifiedCornerCoordinateProjection b L j₀ v ∈
      rowKernel (fun _ : Unit => specifiedCornerCoordinateFunctional b L) := by
  intro _
  rw [specifiedCornerCoordinateProjection_apply, map_sub, map_smul,
    specifiedCornerCoordinateFunctional_single, h₀, smul_eq_mul, mul_one, sub_self]

theorem specifiedCornerCoordinateProjection_fixes (b : Basis J K V) (L : V →ₗ[K] K)
    (j₀ : J) (v : J → K)
    (hv : v ∈ rowKernel (fun _ : Unit => specifiedCornerCoordinateFunctional b L)) :
    specifiedCornerCoordinateProjection b L j₀ v = v := by
  rw [specifiedCornerCoordinateProjection_apply, hv (), zero_smul, sub_zero]

theorem specifiedCornerCoordinateProjection_anchor_zero (b : Basis J K V) (L : V →ₗ[K] K)
    (j₀ : J) (h₀ : L (b j₀) = 1) (_i : Unit) :
    specifiedCornerCoordinateProjection b L j₀ (Pi.single j₀ 1) = 0 := by
  rw [specifiedCornerCoordinateProjection_apply, specifiedCornerCoordinateFunctional_single,
    h₀, one_smul, sub_self]

theorem specifiedCornerCoordinateProjection_free (b : Basis J K V) (L : V →ₗ[K] K)
    (j₀ : J) (v : J → K) (j : originalFreeIndex (fun _ : Unit => j₀)) :
    specifiedCornerCoordinateProjection b L j₀ v j.val = v j.val := by
  have hj : j.val ≠ j₀ := fun h => j.property ⟨(), h.symm⟩
  rw [specifiedCornerCoordinateProjection_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hj, ite_false,
    smul_zero, sub_zero]

/-- Exact coordinate equivalence of the WHOLE specified functional kernel. -/
def specifiedCornerKernelCoordinateEquiv (b : Basis J K V) (L : V →ₗ[K] K) :
    LinearMap.ker L ≃ₗ[K]
      rowKernel (fun _ : Unit => specifiedCornerCoordinateFunctional b L) where
  __ := (b.equivFun.toLinearMap.comp (LinearMap.ker L).subtype).codRestrict _ (by
    intro v _
    change L (b.equivFun.symm (b.equivFun v.val)) = 0
    rw [b.equivFun.symm_apply_apply]
    exact v.property)
  invFun v := ⟨b.equivFun.symm v.val, v.property ()⟩
  left_inv v := Subtype.ext (b.equivFun.symm_apply_apply v.val)
  right_inv v := Subtype.ext (b.equivFun.apply_symm_apply v.val)

/-- Explicit free-coordinate equivalence using the supplied basis and anchor. -/
def specifiedCornerFreeEquiv (b : Basis J K V) (L : V →ₗ[K] K) (j₀ : J)
    (h₀ : L (b j₀) = 1) :
    LinearMap.ker L ≃ₗ[K] (originalFreeIndex (fun _ : Unit => j₀) → K) :=
  (specifiedCornerKernelCoordinateEquiv b L).trans
    (originalFreeKernelEquiv (fun _ : Unit => specifiedCornerCoordinateFunctional b L)
      (fun _ : Unit => j₀) (specifiedCornerCoordinateProjection b L j₀)
      (specifiedCornerCoordinateProjection_mem_kernel b L j₀ h₀)
      (specifiedCornerCoordinateProjection_fixes b L j₀)
      (specifiedCornerCoordinateProjection_anchor_zero b L j₀ h₀)
      (specifiedCornerCoordinateProjection_free b L j₀))

/-- Every non-anchor basis vector, corrected by its actual corner multiple. -/
def specifiedCornerFreeBasis (b : Basis J K V) (L : V →ₗ[K] K) (j₀ : J)
    (h₀ : L (b j₀) = 1) :
    Basis (originalFreeIndex (fun _ : Unit => j₀)) K (LinearMap.ker L) :=
  (Pi.basisFun K (originalFreeIndex (fun _ : Unit => j₀))).map
    (specifiedCornerFreeEquiv b L j₀ h₀).symm

theorem specifiedCornerFreeBasis_vector (b : Basis J K V) (L : V →ₗ[K] K) (j₀ : J)
    (h₀ : L (b j₀) = 1) (j : originalFreeIndex (fun _ : Unit => j₀)) :
    (specifiedCornerFreeBasis b L j₀ h₀ j : V) = b j.val - L (b j.val) • b j₀ := by
  classical
  rw [specifiedCornerFreeBasis, Basis.map_apply, Pi.basisFun_apply]
  change b.equivFun.symm (specifiedCornerCoordinateProjection b L j₀
    (originalFreeExtend (fun _ : Unit => j₀) (Pi.single j 1))) = _
  rw [originalFreeExtend_single, specifiedCornerCoordinateProjection_apply,
    specifiedCornerCoordinateFunctional_single, map_sub, map_smul,
    specifiedBasis_inverse_single, specifiedBasis_inverse_single]

end

end MeyerGeneralProblem.UniformDiscrete
