module

public import MeyerGeneralProblem.UniformDiscrete.FiniteRows

@[expose] public section

/-! Nonzero triangular pivots certify independence of the ORIGINAL rows.
Equal degree keys are permitted: distinct rows of equal degree must have zero
cross-pivot entries. The proof selects a maximal nonzero finite coefficient. -/

namespace MeyerGeneralProblem.UniformDiscrete

noncomputable section

theorem linearIndependent_of_original_triangular_pivots
    {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (row : I → V →ₗ[K] K) (pivot : I → V) (degree : I → ℕ)
    (hdiag : ∀ i, row i (pivot i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → degree i ≤ degree j → row i (pivot j) = 0) :
    LinearIndependent K row := by
  classical
  rw [linearIndependent_iff']
  intro E c hzero i hi
  by_contra hci
  let A : Finset I := E.filter (fun k => c k ≠ 0)
  have hA : A.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image A degree hA
  have hjE : j ∈ E := (Finset.mem_filter.mp hj).1
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hsum : ∑ k ∈ E, c k * row k (pivot j) = 0 := by
    have h := congrArg (fun f : V →ₗ[K] K => f (pivot j)) hzero
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply] using h
  have hsumeq : (∑ k ∈ E, c k * row k (pivot j)) = c j * row j (pivot j) := by
    apply Finset.sum_eq_single j
    · intro k hk hkj
      by_cases hck : c k = 0
      · rw [hck, zero_mul]
      · rw [hoff k j hkj (hmax k (Finset.mem_filter.mpr ⟨hk, hck⟩)), mul_zero]
    · exact fun hjnot => False.elim (hjnot hjE)
  rw [hsumeq] at hsum
  exact mul_ne_zero hcj (hdiag j) hsum

end

end MeyerGeneralProblem.UniformDiscrete
