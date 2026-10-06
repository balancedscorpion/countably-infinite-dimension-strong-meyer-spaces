module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite systems selected from an arbitrary family of linear equations

This is the algebraic part of Iteration 010. The finite rows are selected
from the original index type, not replaced by arbitrary equations defining
the same subspace. No separation, Fourier, or periodic-structure input is
needed here.
-/

namespace MeyerGeneralProblem.UniformDiscrete

open scoped BigOperators

noncomputable section

section Rows

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The simultaneous kernel of all the rows, including an infinite family. -/
def rowKernel (row : I → V →ₗ[K] K) : Submodule K V where
  carrier := {v | ∀ i, row i v = 0}
  zero_mem' := by intro i; exact map_zero (row i)
  add_mem' := by
    intro v w hv hw i
    rw [map_add, hv i, hw i, add_zero]
  smul_mem' := by
    intro a v hv i
    rw [map_smul, hv i, smul_zero]

@[simp]
theorem mem_rowKernel (row : I → V →ₗ[K] K) (v : V) :
    v ∈ rowKernel row ↔ ∀ i, row i v = 0 := Iff.rfl

/-- Evaluate just the selected original rows. The codomain is finite. -/
def selectedRowMap (row : I → V →ₗ[K] K) (s : Finset I) :
    V →ₗ[K] (s → K) where
  toFun v i := row i v
  map_add' := by intro v w; funext i; exact map_add (row i) v w
  map_smul' := by intro a v; funext i; exact map_smul (row i) a v

@[simp]
theorem selectedRowMap_apply (row : I → V →ₗ[K] K)
    (s : Finset I) (v : V) (i : s) :
    selectedRowMap row s v i = row i v := rfl

@[simp]
theorem mem_ker_selectedRowMap (row : I → V →ₗ[K] K)
    (s : Finset I) (v : V) :
    v ∈ LinearMap.ker (selectedRowMap row s) ↔
      ∀ i ∈ s, row i v = 0 := by
  change (fun i : s => row i v) = 0 ↔ _
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i i.property

/-- Adding rows can only shrink the selected kernel. -/
theorem ker_selectedRowMap_antitone (row : I → V →ₗ[K] K)
    {s t : Finset I} (hst : s ⊆ t) :
    LinearMap.ker (selectedRowMap row t) ≤
      LinearMap.ker (selectedRowMap row s) := by
  intro v hv
  exact (mem_ker_selectedRowMap row s v).2 fun i hi =>
    (mem_ker_selectedRowMap row t v).1 hv i (hst hi)

/-- Infinitely many linear equations on a finite-dimensional space have
exactly the same kernel as finitely many of the original equations.

Choose a finite subsystem of minimum kernel dimension. Intersecting it
with any additional row cannot lower that dimension, so cannot change the
kernel. This also covers an empty row type and a zero-dimensional space. -/
theorem exists_selectedRowMap_ker [FiniteDimensional K V]
    (row : I → V →ₗ[K] K) :
    ∃ s : Finset I, LinearMap.ker (selectedRowMap row s) = rowKernel row := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ s : Finset I, Module.finrank K (LinearMap.ker (selectedRowMap row s)) = n
  have hP : ∃ n, P n :=
    ⟨Module.finrank K (LinearMap.ker (selectedRowMap row ∅)), ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hP
  refine ⟨s, le_antisymm ?_ ?_⟩
  · intro v hv i
    have hle : LinearMap.ker (selectedRowMap row (insert i s)) ≤
        LinearMap.ker (selectedRowMap row s) :=
      ker_selectedRowMap_antitone row (Finset.subset_insert i s)
    have hdim : Module.finrank K (LinearMap.ker (selectedRowMap row s)) ≤
        Module.finrank K (LinearMap.ker (selectedRowMap row (insert i s))) := by
      rw [hs]
      exact Nat.find_min' hP ⟨insert i s, rfl⟩
    have heq := Submodule.eq_of_le_of_finrank_le hle hdim
    have hv' : v ∈ LinearMap.ker (selectedRowMap row (insert i s)) := by
      rw [heq]
      exact hv
    exact (mem_ker_selectedRowMap row (insert i s) v).1 hv' i
      (Finset.mem_insert_self i s)
  · intro v hv
    exact (mem_ker_selectedRowMap row s v).2 fun i _ => hv i

/-- A finite subsystem really tests every row, not just a necessary condition. -/
theorem exists_selected_rows_iff [FiniteDimensional K V]
    (row : I → V →ₗ[K] K) :
    ∃ s : Finset I, ∀ v : V,
      (∀ i, row i v = 0) ↔ ∀ i ∈ s, row i v = 0 := by
  obtain ⟨s, hs⟩ := exists_selectedRowMap_ker row
  refine ⟨s, fun v => ?_⟩
  rw [← mem_rowKernel, ← hs, mem_ker_selectedRowMap]

end Rows

section Synthesis

variable {K V W I : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

/-- Finite-kernel reduction for an injectively parametrised subspace.

The completeness hypothesis says every element of `P` is synthesised;
the support equivalence imposes all original rows on a synthesised vector.
Neither hypothesis is inferred from finite dimensionality. -/
theorem finiteKernel_of_injective_synthesis
    (P : Submodule K W) (synthesis : V →ₗ[K] W)
    (row : I → V →ₗ[K] K)
    (hinjective : Function.Injective synthesis)
    (hcomplete : ∀ w ∈ P, ∃ v, synthesis v = w)
    (hsupport : ∀ v, synthesis v ∈ P ↔ v ∈ rowKernel row) :
    ∃ s : Finset I,
      FiniteDimensional K P ∧
      Nonempty (P ≃ₗ[K] LinearMap.ker (selectedRowMap row s)) ∧
      Module.finrank K P +
          Module.finrank K (LinearMap.range (selectedRowMap row s)) =
        Module.finrank K V ∧
      Module.finrank K P = Module.finrank K V -
        Module.finrank K (LinearMap.range (selectedRowMap row s)) := by
  classical
  obtain ⟨s, hs⟩ := exists_selectedRowMap_ker row
  let F : LinearMap.ker (selectedRowMap row s) →ₗ[K] P :=
    { toFun := fun v => ⟨synthesis v, (hsupport v).2 (hs ▸ v.property)⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        exact map_add synthesis (v : V) (w : V)
      map_smul' := by
        intro a v
        apply Subtype.ext
        exact map_smul synthesis a (v : V) }
  have hF : Function.Bijective F := by
    constructor
    · intro v w h
      apply Subtype.ext
      apply hinjective
      exact congrArg Subtype.val h
    · intro w
      obtain ⟨v, hv⟩ := hcomplete w w.property
      have hvP : synthesis v ∈ P := by rw [hv]; exact w.property
      have hvK : v ∈ LinearMap.ker (selectedRowMap row s) :=
        hs.symm ▸ (hsupport v).1 hvP
      exact ⟨⟨v, hvK⟩, Subtype.ext hv⟩
  let e : LinearMap.ker (selectedRowMap row s) ≃ₗ[K] P :=
    LinearEquiv.ofBijective F hF
  letI : FiniteDimensional K P := Module.Finite.equiv e
  have he : Module.finrank K P =
      Module.finrank K (LinearMap.ker (selectedRowMap row s)) :=
    e.symm.finrank_eq
  have hr := LinearMap.finrank_range_add_finrank_ker (selectedRowMap row s)
  refine ⟨s, inferInstance, ⟨e.symm⟩, ?_, ?_⟩ <;> omega

end Synthesis

section Matrices

variable {K I J : Type*} [Field K] [Fintype J] [DecidableEq J]

/-- The actual matrix of the selected original rows in standard coordinates. -/
def selectedRowMatrix (row : I → (J → K) →ₗ[K] K) (s : Finset I) :
    Matrix s J K := fun i j => row i (Pi.single j 1)

/-- The finite row map and the displayed finite matrix have identical action. -/
theorem selectedRowMatrix_mulVec
    (row : I → (J → K) →ₗ[K] K) (s : Finset I) (v : J → K) :
    (selectedRowMatrix row s).mulVec v = selectedRowMap row s v := by
  classical
  funext i
  have hv : v = ∑ j : J, v j • Pi.single j (1 : K) := by
    funext j
    simp [Pi.single_apply]
  change (∑ j : J, row i (Pi.single j 1) * v j) = row i v
  calc
    (∑ j : J, row i (Pi.single j 1) * v j) =
        ∑ j : J, row i (v j • Pi.single j (1 : K)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul, mul_comm]
    _ = row i (∑ j : J, v j • Pi.single j (1 : K)) :=
      (map_sum (row i) _ _).symm
    _ = row i v := congrArg (row i) hv.symm

end Matrices

end

end MeyerGeneralProblem.UniformDiscrete
