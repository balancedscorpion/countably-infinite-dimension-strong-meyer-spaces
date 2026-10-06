module

public import MeyerGeneralProblem.UniformDiscrete.FiniteRows
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-! Exact whole-kernel dimension for independent ORIGINAL finite rows.
The full row kernel is identified with the actual dual coannihilator. -/

namespace MeyerGeneralProblem.UniformDiscrete

noncomputable section

theorem rowKernel_eq_dualCoannihilator {K V I : Type*}
    [Field K] [AddCommGroup V] [Module K V] (row : I → V →ₗ[K] K) :
    rowKernel row = (Submodule.span K (Set.range row)).dualCoannihilator := by
  ext v
  change (∀ i, row i v = 0) ↔
    v ∈ ((Submodule.span K (Set.range row)).dualCoannihilator : Set V)
  rw [Submodule.coe_dualCoannihilator_span]
  constructor
  · intro h f hf
    obtain ⟨i, rfl⟩ := hf
    exact h i
  · intro h i
    exact h _ ⟨i, rfl⟩

theorem finrank_rowKernel_add_card_of_linearIndependent {K V I : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype I]
    (row : I → V →ₗ[K] K) (hrow : LinearIndependent K row) :
    Module.finrank K (rowKernel row) + Fintype.card I = Module.finrank K V := by
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (Submodule.span K (Set.range row))
  rw [← rowKernel_eq_dualCoannihilator, finrank_span_eq_card hrow] at h
  omega

theorem finrank_rowKernel_of_linearIndependent {K V I : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype I]
    (row : I → V →ₗ[K] K) (hrow : LinearIndependent K row) :
    Module.finrank K (rowKernel row) = Module.finrank K V - Fintype.card I := by
  have h := finrank_rowKernel_add_card_of_linearIndependent row hrow
  omega

end

end MeyerGeneralProblem.UniformDiscrete
