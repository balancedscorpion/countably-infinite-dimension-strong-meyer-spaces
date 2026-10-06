module

public import MeyerGeneralProblem.UniformDiscrete.OriginalRowBasisSelection

@[expose] public section

/-! A specified ORIGINAL finite row matrix, invertible on the whole corner-zero
space, cuts the whole original space to a line with corner one. This applies to
an already selected tuple; it does not replace it by a new existential selector. -/

namespace MeyerGeneralProblem.UniformDiscrete

open Module

noncomputable section

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype I] [DecidableEq I]

/-- Typed whole finite evaluation matrix on a specified corner-zero basis. -/
def originalCornerEvaluationMatrix (row : I → V →ₗ[K] K) (J : V →ₗ[K] K)
    (b : Basis I K (LinearMap.ker J)) : Matrix I I K :=
  fun i j => row i (b j).val

/-- Nonzero determinant separates EVERY vector of the complete corner-zero space. -/
theorem originalCornerEvaluationMatrix_separates (row : I → V →ₗ[K] K) (J : V →ₗ[K] K)
    (b : Basis I K (LinearMap.ker J))
    (hd : (originalCornerEvaluationMatrix row J b).det ≠ 0)
    (w : LinearMap.ker J) (hw : ∀ i, row i w.val = 0) : w = 0 := by
  classical
  by_contra hn
  have hc : b.equivFun w ≠ 0 := by
    intro hz
    apply hn
    exact b.equivFun.injective (by simpa only [map_zero] using hz)
  apply hd
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨b.equivFun w, hc, ?_⟩
  funext i
  have h := congrArg (fun v : LinearMap.ker J => row i v.val) (b.sum_equivFun w)
  simpa only [originalCornerEvaluationMatrix, Matrix.mulVec, dotProduct,
    Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul,
    mul_comm, Pi.zero_apply, hw i] using h

/-- The full evaluation map for the prescribed finite row tuple. -/
def originalFiniteEvaluationMap (row : I → V →ₗ[K] K) : V →ₗ[K] (I → K) where
  toFun v i := row i v
  map_add' v w := by funext i; exact (row i).map_add v w
  map_smul' c v := by funext i; exact (row i).map_smul c v

/-- ALL prescribed original rows cut the same whole kernel as their evaluation map. -/
theorem rowKernel_eq_originalFiniteEvaluationKer (row : I → V →ₗ[K] K) :
    rowKernel row = LinearMap.ker (originalFiniteEvaluationMap row) := by
  ext v
  change (∀ i, row i v = 0) ↔ (fun i => row i v) = 0
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- A prescribed invertible complete W matrix leaves exactly one complete line,
with the actual corner functional normalized to one. -/
theorem originalCornerDeterminant_complete_line (row : I → V →ₗ[K] K) (J : V →ₗ[K] K)
    (b : Basis I K (LinearMap.ker J))
    (hd : (originalCornerEvaluationMatrix row J b).det ≠ 0)
    (hJ : J ≠ 0) :
    Module.finrank K (rowKernel row) = 1 ∧ ∃ v ∈ rowKernel row, J v = 1 := by
  classical
  let A := rowKernel row
  have hsep (v : V) (hv : v ∈ A) (hj : J v = 0) : v = 0 := by
    have hw := originalCornerEvaluationMatrix_separates row J b hd ⟨v, hj⟩ hv
    exact congrArg Subtype.val hw
  let f : A →ₗ[K] K := J.comp A.subtype
  have hf : Function.Injective f := by
    intro a c hac
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hsep _ (A.sub_mem a.property c.property)
    rw [map_sub]
    exact sub_eq_zero.mpr hac
  have hu : Module.finrank K A ≤ 1 := by
    simpa using f.finrank_le_finrank_of_injective hf
  have hW : Module.finrank K (LinearMap.ker J) + 1 = Module.finrank K V :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hJ
  have hc := Module.finrank_eq_card_basis b
  have hn := (originalFiniteEvaluationMap row).finrank_range_add_finrank_ker
  have hr : Module.finrank K (LinearMap.range (originalFiniteEvaluationMap row)) ≤ Fintype.card I := by
    simpa using (LinearMap.range (originalFiniteEvaluationMap row)).finrank_le
  have hk : Module.finrank K (LinearMap.ker (originalFiniteEvaluationMap row)) = Module.finrank K A := by
    rw [← rowKernel_eq_originalFiniteEvaluationKer]
  have hl : 1 ≤ Module.finrank K A := by omega
  have hdim : Module.finrank K A = 1 := Nat.le_antisymm hu hl
  have hbot : A ≠ ⊥ := Submodule.one_le_finrank_iff.mp hl
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ A, v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hbot
    apply le_antisymm _ bot_le
    intro v hv
    exact (Submodule.mem_bot K).mpr (hn v hv)
  have hj : J v ≠ 0 := fun hz => hv0 (hsep v hv hz)
  refine ⟨hdim, (J v)⁻¹ • v, A.smul_mem _ hv, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hj]

end

end MeyerGeneralProblem.UniformDiscrete
