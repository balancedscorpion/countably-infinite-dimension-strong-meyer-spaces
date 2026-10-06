module

public import MeyerGeneralProblem.Cardinal.Strong.RationalComplexArithmetic
public import Mathlib.Data.Finset.Fold
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-! Ordinary exact Gaussian-rational determinant arithmetic. Every permutation
and every matrix factor is retained in the finite Leibniz program. -/

namespace MeyerGeneralProblem.StrongParity

/-- Exact rational complex multiplication is commutative. -/
instance rationalComplexMul_commutative : Std.Commutative rationalComplexMul where
  comm a b := by apply Prod.ext <;> simp only [rationalComplexMul] <;> ring

/-- Exact rational complex multiplication is associative. -/
instance rationalComplexMul_associative : Std.Associative rationalComplexMul where
  assoc a b c := by apply Prod.ext <;> simp only [rationalComplexMul] <;> ring

/-- Complete ordinary finite product of rational complex factors. -/
def rationalComplexProd {ι : Type*} (A : Finset ι) (f : ι → ℚ × ℚ) : ℚ × ℚ :=
  A.fold rationalComplexMul (1, 0) f

/-- Ordinary rational representation of the exact permutation sign. -/
def rationalPermutationSign {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Equiv.Perm ι) : ℚ × ℚ := (((Equiv.Perm.sign p : ℤ) : ℚ), 0)

/-- Complete finite Gaussian-rational Leibniz determinant program. -/
def rationalComplexDet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ℚ × ℚ)) : ℚ × ℚ :=
  rationalComplexSum Finset.univ (fun p : Equiv.Perm ι =>
    rationalComplexMul (rationalPermutationSign p)
      (rationalComplexProd Finset.univ (fun i => M (p i) i)))

noncomputable section

/-- Typed complex matrix value of the ordinary rational-coordinate matrix. -/
def rationalComplexMatrixValue {ι : Type*} (M : Matrix ι ι (ℚ × ℚ)) : Matrix ι ι ℂ :=
  fun i j => rationalComplexValue (M i j)

/-- Every complete rational product has exactly its literal complex product value. -/
theorem rationalComplexProd_value {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (f : ι → ℚ × ℚ) :
    rationalComplexValue (rationalComplexProd A f) = ∏ i ∈ A, rationalComplexValue (f i) := by
  induction A using Finset.induction_on with
  | empty => simp [rationalComplexProd, rationalComplexValue]
  | @insert a A ha ih =>
    rw [rationalComplexProd, Finset.fold_insert ha, rationalComplexMul_value]
    rw [← rationalComplexProd, ih, Finset.prod_insert ha]

/-- The ordinary sign representation is exactly the original determinant sign. -/
theorem rationalPermutationSign_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Equiv.Perm ι) :
    rationalComplexValue (rationalPermutationSign p) = ((Equiv.Perm.sign p : ℤ) : ℂ) := by
  simp [rationalPermutationSign, rationalComplexValue]

/-- Every exact permutation sign has complex norm one. -/
theorem rationalPermutationSign_norm_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Equiv.Perm ι) : ‖rationalComplexValue (rationalPermutationSign p)‖ = 1 := by
  rw [rationalPermutationSign_value, Complex.norm_intCast]
  exact_mod_cast Equiv.Perm.sign_abs p

/-- The complete ordinary rational program equals the actual matrix determinant. -/
theorem rationalComplexDet_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ℚ × ℚ)) :
    rationalComplexValue (rationalComplexDet M) =
      Matrix.det (rationalComplexMatrixValue M) := by
  rw [rationalComplexDet, rationalComplexSum_value, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [rationalComplexMul_value, rationalPermutationSign_value, rationalComplexProd_value]
  simp only [Finset.mem_univ, Units.smul_def, zsmul_eq_mul,
    rationalComplexMatrixValue]

end

end MeyerGeneralProblem.StrongParity
