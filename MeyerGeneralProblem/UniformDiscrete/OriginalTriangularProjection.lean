module

public import MeyerGeneralProblem.UniformDiscrete.OriginalDegreeElimination

@[expose] public section

/-! A definite finite projection from original degree elimination.
All original rows below the bound vanish, the complete original row kernel
is fixed, original pivots vanish, and every pivot-annihilating functional
is preserved. No arbitrary complement or unknown minor is selected. -/

namespace MeyerGeneralProblem.UniformDiscrete

noncomputable section

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]

/-- Compose original degree steps `0,...,n-1`, in that order. -/
def originalDegreeElimination (row : I → V →ₗ[K] K) (pivot : I → V)
    (degree : I → ℕ) : ℕ → V →ₗ[K] V
  | 0 => LinearMap.id
  | n + 1 => (originalDegreeEliminationStep row pivot degree n).comp
      (originalDegreeElimination row pivot degree n)

theorem originalDegreeElimination_row_zero (row : I → V →ₗ[K] K) (pivot : I → V)
    (degree : I → ℕ) (hdiag : ∀ i, row i (pivot i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → degree i ≤ degree j → row i (pivot j) = 0)
    (n : ℕ) (i : I) (hi : degree i < n) (v : V) :
    row i (originalDegreeElimination row pivot degree n v) = 0 := by
  have h : ∀ n i v, degree i < n →
      row i (originalDegreeElimination row pivot degree n v) = 0 := by
    intro n
    induction n with
    | zero => intro i v hi; omega
    | succ n ih =>
      intro i v hi
      rw [originalDegreeElimination, LinearMap.comp_apply]
      by_cases heq : degree i = n
      · exact originalDegreeEliminationStep_row_of_eq row pivot degree hdiag hoff n i heq _
      · have hlt : degree i < n := by omega
        rw [originalDegreeEliminationStep_row_of_lt row pivot degree hoff n i hlt]
        exact ih i v hlt
  exact h n i v hi

theorem originalDegreeElimination_fixes_rowKernel (row : I → V →ₗ[K] K)
    (pivot : I → V) (degree : I → ℕ) (n : ℕ) (v : V) (hv : v ∈ rowKernel row) :
    originalDegreeElimination row pivot degree n v = v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [originalDegreeElimination, LinearMap.comp_apply, ih]
    exact originalDegreeEliminationStep_fixes row pivot degree n v (fun i _ => hv i)

theorem originalDegreeElimination_pivot_of_le (row : I → V →ₗ[K] K) (pivot : I → V)
    (degree : I → ℕ)
    (hoff : ∀ i j, i ≠ j → degree i ≤ degree j → row i (pivot j) = 0)
    (n : ℕ) (j : I) (hj : n ≤ degree j) :
    originalDegreeElimination row pivot degree n (pivot j) = pivot j := by
  have h : ∀ n j, n ≤ degree j →
      originalDegreeElimination row pivot degree n (pivot j) = pivot j := by
    intro n
    induction n with
    | zero => intro j _; rfl
    | succ n ih =>
      intro j hj
      rw [originalDegreeElimination, LinearMap.comp_apply, ih j (by omega)]
      exact originalDegreeEliminationStep_pivot_of_lt row pivot degree hoff n j (by omega)
  exact h n j hj

theorem originalDegreeElimination_pivot_zero (row : I → V →ₗ[K] K) (pivot : I → V)
    (degree : I → ℕ) (hdiag : ∀ i, row i (pivot i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → degree i ≤ degree j → row i (pivot j) = 0)
    (n : ℕ) (j : I) (hj : degree j < n) :
    originalDegreeElimination row pivot degree n (pivot j) = 0 := by
  have h : ∀ n j, degree j < n →
      originalDegreeElimination row pivot degree n (pivot j) = 0 := by
    intro n
    induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      intro j hj
      rw [originalDegreeElimination, LinearMap.comp_apply]
      by_cases heq : degree j = n
      · rw [originalDegreeElimination_pivot_of_le row pivot degree hoff n j (by omega)]
        exact originalDegreeEliminationStep_pivot_of_eq row pivot degree hdiag hoff n j heq
      · rw [ih j (by omega), map_zero]
  exact h n j hj

theorem originalDegreeElimination_preserves_functional (row : I → V →ₗ[K] K)
    (pivot : I → V) (degree : I → ℕ) (n : ℕ) (L : V →ₗ[K] K)
    (hL : ∀ i, L (pivot i) = 0) (v : V) :
    L (originalDegreeElimination row pivot degree n v) = L v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [originalDegreeElimination, LinearMap.comp_apply,
      originalDegreeEliminationStep_preserves_functional row pivot degree n L hL, ih]

omit [Fintype I] in
theorem original_triangular_pivot_injective (row : I → V →ₗ[K] K) (pivot : I → V)
    (degree : I → ℕ) (hdiag : ∀ i, row i (pivot i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → degree i ≤ degree j → row i (pivot j) = 0) :
    Function.Injective pivot := by
  intro i j heq
  by_contra hij
  rcases le_total (degree i) (degree j) with hd | hd
  · exact hdiag i ((congrArg (row i) heq).trans (hoff i j hij hd))
  · exact hdiag j ((congrArg (row j) heq.symm).trans (hoff j i (fun h => hij h.symm) hd))

end

end MeyerGeneralProblem.UniformDiscrete
