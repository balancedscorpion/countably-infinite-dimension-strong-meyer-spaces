module

public import MeyerGeneralProblem.Cardinal.Strong.LaurentCharacterTwists
public import MeyerGeneralProblem.Cardinal.Strong.FiniteArrayNumerator

@[expose] public section

/-! Algebra action of finite Laurent polynomials on unrestricted whole arrays.
Multiplication supplies convolution associativity without any convergence or
finite-support assumption on the array. -/
namespace MeyerGeneralProblem
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- The literal signed shift on the WHOLE original array space. -/
def originalLaurentArrayShift (m : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u n := u (n - m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual shifts compose by addition of their whole integer labels. -/
def originalLaurentArrayShiftHom : Multiplicative G →* Module.End ℂ (G → ℂ) where
  toFun m := originalLaurentArrayShift m.toAdd
  map_one' := by ext u n; simp [originalLaurentArrayShift]
  map_mul' m l := by
    ext u n
    change u (n - (m.toAdd + l.toAdd)) = u ((n - m.toAdd) - l.toAdd)
    congr 1
    abel

/-- The true algebra representation on unrestricted arrays, by finite Laurent convolution. -/
def originalLaurentArrayAction : AddMonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ (G → ℂ) :=
  AddMonoidAlgebra.lift ℂ (Module.End ℂ (G → ℂ)) G originalLaurentArrayShiftHom

/-- Its action is EXACTLY the original all-label annihilator convolution. -/
theorem originalLaurentArrayAction_apply (p : AddMonoidAlgebra ℂ G) (u : G → ℂ) (n : G) :
    originalLaurentArrayAction p u n = annihilatorArrayConvolution p.coeff u n := by
  classical
  rw [originalLaurentArrayAction, AddMonoidAlgebra.lift_apply]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, annihilatorArrayConvolution]
  rfl

/-- Finite polynomial multiplication acts associatively on EVERY unrestricted array. -/
theorem annihilatorArrayConvolution_mul (p q : AddMonoidAlgebra ℂ G) (u : G → ℂ) (n : G) :
    annihilatorArrayConvolution (p * q).coeff u n =
      annihilatorArrayConvolution p.coeff (annihilatorArrayConvolution q.coeff u) n := by
  rw [← originalLaurentArrayAction_apply, map_mul]
  change originalLaurentArrayAction p (originalLaurentArrayAction q u) n = _
  rw [originalLaurentArrayAction_apply]
  congr 1
  funext m
  exact originalLaurentArrayAction_apply q u m

/-- On a finite coefficient array the action is EXACTLY Laurent polynomial multiplication. -/
theorem annihilatorArrayConvolution_finite (p q : AddMonoidAlgebra ℂ G) (n : G) :
    annihilatorArrayConvolution p.coeff (fun m => q.coeff m) n = (p * q).coeff n := by
  classical
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  unfold annihilatorArrayConvolution Finsupp.sum
  apply Finset.sum_congr rfl
  intro m _
  congr 2
  abel

/-- Both additive array operations are respected by the actual finite convolution. -/
theorem annihilatorArrayConvolution_zero (p : G →₀ ℂ) (n : G) :
    annihilatorArrayConvolution p (0 : G → ℂ) n = 0 := by
  simp [annihilatorArrayConvolution]

end
end MeyerGeneralProblem
