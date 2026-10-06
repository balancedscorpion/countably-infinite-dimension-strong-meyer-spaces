module

public import MeyerGeneralProblem.UniformDiscrete.TriangularOriginalRows

@[expose] public section

/-! Finite elimination using ONLY original triangular pivot entries.
Each step divides by the specified diagonal, with no rank/minor zero search.
All lower-degree original rows are preserved while the current degree is killed. -/

namespace MeyerGeneralProblem.UniformDiscrete

noncomputable section

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]

/-- Cancel one degree using the literal original rows and pivot vectors. -/
def originalDegreeEliminationStep (row : I → V →ₗ[K] K) (pivot : I → V)
    (degree : I → ℕ) (t : ℕ) : V →ₗ[K] V :=
  LinearMap.id - ∑ i ∈ Finset.univ.filter (fun i => degree i = t),
    (row i).smulRight ((row i (pivot i))⁻¹ • pivot i)

theorem originalDegreeEliminationStep_apply (row : I → V →ₗ[K] K) (pivot : I → V)
    (degree : I → ℕ) (t : ℕ) (v : V) :
    originalDegreeEliminationStep row pivot degree t v =
      v - ∑ i ∈ Finset.univ.filter (fun i => degree i = t),
        (row i v / row i (pivot i)) • pivot i := by
  simp only [originalDegreeEliminationStep, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, smul_smul, div_eq_mul_inv]

theorem originalDegreeEliminationStep_row_of_lt (row : I → V →ₗ[K] K) (pivot : I → V)
    (degree : I → ℕ)
    (hoff : ∀ i j, i ≠ j → degree i ≤ degree j → row i (pivot j) = 0)
    (t : ℕ) (i : I) (hi : degree i < t) (v : V) :
    row i (originalDegreeEliminationStep row pivot degree t v) = row i v := by
  classical
  rw [originalDegreeEliminationStep_apply, map_sub, map_sum]
  have hz : (∑ j ∈ Finset.univ.filter (fun j => degree j = t),
      row i ((row j v / row j (pivot j)) • pivot j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjt := (Finset.mem_filter.mp hj).2
    rw [map_smul, hoff i j (by intro heq; subst j; omega) (by omega), smul_zero]
  rw [hz, sub_zero]

theorem originalDegreeEliminationStep_row_of_eq (row : I → V →ₗ[K] K) (pivot : I → V)
    (degree : I → ℕ) (hdiag : ∀ i, row i (pivot i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → degree i ≤ degree j → row i (pivot j) = 0)
    (t : ℕ) (i : I) (hi : degree i = t) (v : V) :
    row i (originalDegreeEliminationStep row pivot degree t v) = 0 := by
  classical
  rw [originalDegreeEliminationStep_apply, map_sub, map_sum]
  have heq : (∑ j ∈ Finset.univ.filter (fun j => degree j = t),
      row i ((row j v / row j (pivot j)) • pivot j)) = row i v := by
    rw [Finset.sum_eq_single i]
    · rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (hdiag i)]
    · intro j hj hji
      have hjt := (Finset.mem_filter.mp hj).2
      rw [map_smul, hoff i j hji.symm (by omega), smul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩))
  rw [heq, sub_self]

theorem originalDegreeEliminationStep_fixes (row : I → V →ₗ[K] K) (pivot : I → V)
    (degree : I → ℕ) (t : ℕ) (v : V) (hv : ∀ i, degree i = t → row i v = 0) :
    originalDegreeEliminationStep row pivot degree t v = v := by
  rw [originalDegreeEliminationStep_apply]
  have hz : (∑ i ∈ Finset.univ.filter (fun i => degree i = t),
      (row i v / row i (pivot i)) • pivot i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hv i (Finset.mem_filter.mp hi).2, zero_div, zero_smul]
  rw [hz, sub_zero]

theorem originalDegreeEliminationStep_pivot_of_lt (row : I → V →ₗ[K] K)
    (pivot : I → V) (degree : I → ℕ)
    (hoff : ∀ i j, i ≠ j → degree i ≤ degree j → row i (pivot j) = 0)
    (t : ℕ) (j : I) (hj : t < degree j) :
    originalDegreeEliminationStep row pivot degree t (pivot j) = pivot j := by
  apply originalDegreeEliminationStep_fixes
  intro i hi
  exact hoff i j (by intro heq; subst j; omega) (by omega)

theorem originalDegreeEliminationStep_pivot_of_eq (row : I → V →ₗ[K] K)
    (pivot : I → V) (degree : I → ℕ) (hdiag : ∀ i, row i (pivot i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → degree i ≤ degree j → row i (pivot j) = 0)
    (t : ℕ) (j : I) (hj : degree j = t) :
    originalDegreeEliminationStep row pivot degree t (pivot j) = 0 := by
  classical
  rw [originalDegreeEliminationStep_apply]
  have heq : (∑ i ∈ Finset.univ.filter (fun i => degree i = t),
      (row i (pivot j) / row i (pivot i)) • pivot i) = pivot j := by
    rw [Finset.sum_eq_single j]
    · rw [div_self (hdiag j), one_smul]
    · intro i hi hij
      have hit := (Finset.mem_filter.mp hi).2
      rw [hoff i j hij (by omega), zero_div, zero_smul]
    · intro hn
      exact False.elim (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))
  rw [heq, sub_self]

theorem originalDegreeEliminationStep_preserves_functional (row : I → V →ₗ[K] K)
    (pivot : I → V) (degree : I → ℕ) (t : ℕ) (L : V →ₗ[K] K)
    (hL : ∀ i, L (pivot i) = 0) (v : V) :
    L (originalDegreeEliminationStep row pivot degree t v) = L v := by
  rw [originalDegreeEliminationStep_apply, map_sub, map_sum]
  have hz : (∑ i ∈ Finset.univ.filter (fun i => degree i = t),
      L ((row i v / row i (pivot i)) • pivot i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul, hL i, smul_zero]
  rw [hz, sub_zero]

end

end MeyerGeneralProblem.UniformDiscrete
