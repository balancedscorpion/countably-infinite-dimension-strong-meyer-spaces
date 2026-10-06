module

public import MeyerGeneralProblem.Cardinal.Strong.SheetHomogeneousOrbit
public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalPolynomial

@[expose] public section

/-! Actual two-variable polynomial evaluation and literal homogeneous sheet
coefficients. The original quarter phase is inserted exactly once, after the
native coordinate powers, including on the infinity charts. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual native nonnegative-coordinate monomial at arbitrary complex coordinates. -/
def originalPositiveTorusMonomial (Z W : ℂ) : Multiplicative (ℕ × ℕ) →* ℂ where
  toFun n := Z ^ n.toAdd.1 * W ^ n.toAdd.2
  map_one' := by simp
  map_mul' n l := by
    change Z ^ (n.toAdd.1 + l.toAdd.1) * W ^ (n.toAdd.2 + l.toAdd.2) = _
    simp only [pow_add]
    ac_rfl

/-- Genuine algebra evaluation on arbitrary complex coordinates, retaining ALL collisions. -/
def originalPositiveTorusEvaluation (Z W : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℕ) →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (ℕ × ℕ) (originalPositiveTorusMonomial Z W)

/-- The literal finite monomial coefficient is evaluated exactly once. -/
theorem originalPositiveTorusEvaluation_single (Z W : ℂ) (n : ℕ × ℕ) (c : ℂ) :
    originalPositiveTorusEvaluation Z W (AddMonoidAlgebra.single n c) = c * (Z ^ n.1 * W ^ n.2) := by
  rw [originalPositiveTorusEvaluation, AddMonoidAlgebra.lift_single]
  rfl

/-- Literal bihomogeneous sheet with its original quarter phase, NEVER its dilation power. -/
def originalPositiveSheetHomogeneous (d : ℕ) (a : ℝ) (z₀ z₁ w₀ w₁ : ℂ) : ℂ :=
  originalHomogeneousSheet a (z₀ ^ d) (z₁ ^ d) (w₀ ^ d) (complexUnitPhase (-1 / 4) * w₁ ^ d)

/-- The true affine chart of the homogeneous sheet equals the ACTUAL native polynomial. -/
theorem originalPositiveSheetHomogeneous_affine (d : ℕ) (a : ℝ) (Z W : ℂ) :
    originalPositiveSheetHomogeneous d a 1 Z 1 W =
      originalPositiveTorusEvaluation Z W (originalPositiveSheetPolynomial d a) := by
  simp only [originalPositiveSheetHomogeneous, one_pow, originalPositiveSheetPolynomial,
    map_sub, map_add, originalPositiveTorusEvaluation_single, pow_zero, one_mul, mul_one]
  unfold originalHomogeneousSheet
  ring

/-- Every native sheet has the exact common bidegree under BOTH homogeneous scalings. -/
theorem originalPositiveSheetHomogeneous_scale (d : ℕ) (a : ℝ)
    (z₀ z₁ w₀ w₁ ρ σ : ℂ) :
    originalPositiveSheetHomogeneous d a (ρ * z₀) (ρ * z₁) (σ * w₀) (σ * w₁) =
      ρ ^ d * σ ^ d * originalPositiveSheetHomogeneous d a z₀ z₁ w₀ w₁ := by
  simp only [originalPositiveSheetHomogeneous, originalHomogeneousSheet, mul_pow]
  ring

/-- The original quarter phase is nonzero, including at every chart boundary. -/
theorem originalQuarterPhase_ne_zero : complexUnitPhase (-1 / 4) ≠ 0 := by
  exact Complex.exp_ne_zero _

end
end MeyerGeneralProblem.StrongParity
