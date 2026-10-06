module

public import MeyerGeneralProblem.Cardinal.Strong.FiniteComplexElimination
public import MeyerGeneralProblem.UniformDiscrete.OriginalTriangularProjection

@[expose] public section

/-! The complete coordinate algorithm is literally the repository's original
finite projection when supplied its original rows and exact diagonal inverses. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Equality on the WHOLE vector, without a complement, rank oracle or omitted row. -/
theorem complexCoordinateDegreeElimination_eq_original {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (row : I → (J → ℂ) →ₗ[ℂ] ℂ) (pivot : I → J) (degree : I → ℕ)
    (t : ℕ) (v : J → ℂ) (j : J) :
    complexCoordinateDegreeElimination (fun i k => row i (Pi.single k 1))
      (fun i => (row i (Pi.single (pivot i) 1))⁻¹) pivot degree t v j =
    UniformDiscrete.originalDegreeElimination row
      (fun i => Pi.single (pivot i) 1) degree t v j := by
  induction t generalizing j with
  | zero => rfl
  | succ t ih =>
    have hw : (fun k => complexCoordinateDegreeElimination
        (fun i k => row i (Pi.single k 1))
        (fun i => (row i (Pi.single (pivot i) 1))⁻¹) pivot degree t v k) =
        UniformDiscrete.originalDegreeElimination row
          (fun i => Pi.single (pivot i) 1) degree t v := funext ih
    simp only [complexCoordinateDegreeElimination, hw,
      UniformDiscrete.originalDegreeElimination, LinearMap.comp_apply,
      UniformDiscrete.originalDegreeEliminationStep_apply, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Finset.sum_filter, div_eq_mul_inv]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← finiteLinearRow_eq_coordinate_dot]
    by_cases hd : degree i = t <;> by_cases hp : j = pivot i <;> simp [hd, hp, eq_comm]

end

end MeyerGeneralProblem.StrongParity
