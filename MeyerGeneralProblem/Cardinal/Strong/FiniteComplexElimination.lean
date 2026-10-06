module

public import MeyerGeneralProblem.Cardinal.Strong.RationalComplexArithmetic

@[expose] public section

/-! Literal complete coordinate degree elimination and its rational value bridge.
This finite algorithm uses the specified pivot coordinate and inverse at each row. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Literal finite coordinate elimination on the entire vector. -/
def complexCoordinateDegreeElimination {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (row : I → J → ℂ)
    (inverse : I → ℂ) (pivot : I → J) (degree : I → ℕ) : ℕ → (J → ℂ) → J → ℂ
  | 0, v => v
  | t + 1, v =>
    let w := complexCoordinateDegreeElimination row inverse pivot degree t v
    fun j => w j - ∑ i ∈ Finset.univ.filter (fun i => degree i = t ∧ pivot i = j),
      (∑ k : J, row i k * w k) * inverse i

/-- Every computed rational coordinate has the value of the literal complete elimination. -/
theorem rationalComplexDegreeElimination_value {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (row : I → J → ℚ × ℚ)
    (inverse : I → ℚ × ℚ) (pivot : I → J) (degree : I → ℕ)
    (t : ℕ) (v : J → ℚ × ℚ) (j : J) :
    rationalComplexValue (rationalComplexDegreeElimination row inverse pivot degree t v j) =
      complexCoordinateDegreeElimination (fun i k => rationalComplexValue (row i k))
        (fun i => rationalComplexValue (inverse i)) pivot degree t
        (fun k => rationalComplexValue (v k)) j := by
  induction t generalizing j with
  | zero => rfl
  | succ t ih =>
    simp only [rationalComplexDegreeElimination, complexCoordinateDegreeElimination,
      rationalComplexSub_value, rationalComplexSum_value, rationalComplexMul_value,
      rationalComplexDot_value, ih]

/-- Every complete complex linear row is its monomial coordinate dot product. -/
theorem finiteLinearRow_eq_coordinate_dot {J : Type*} [Fintype J] [DecidableEq J]
    (row : (J → ℂ) →ₗ[ℂ] ℂ) (v : J → ℂ) :
    row v = ∑ j : J, row (Pi.single j 1) * v j := by
  have hv : v = ∑ j : J, v j • Pi.single j (1 : ℂ) := by
    funext k
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  simp only [smul_eq_mul]
  ring

end

end MeyerGeneralProblem.StrongParity
