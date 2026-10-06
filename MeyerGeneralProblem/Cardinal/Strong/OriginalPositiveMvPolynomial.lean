module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalChartPoleCancellation
public import Mathlib.RingTheory.Nullstellensatz

@[expose] public section

/-! Exact two-coordinate transport for the actual polynomial orbit partition.
The genuine coefficient algebra and its arbitrary complex evaluations agree
with two-variable MvPolynomial; no generic evaluation certificate is used. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Both native nonnegative coordinate exponents, with no row discarded. -/
def originalNativeMvExponentEquiv : (ℕ × ℕ) ≃+ (Fin 2 →₀ ℕ) where
  toFun n := Finsupp.single 0 n.1 + Finsupp.single 1 n.2
  invFun n := (n 0, n 1)
  left_inv n := by simp
  right_inv n := by
    ext i
    fin_cases i <;> simp
  map_add' n m := by
    ext i
    fin_cases i <;> simp

/-- Genuine complex polynomial algebra equivalence for the actual native coefficients. -/
def originalPositiveMvEquiv : AddMonoidAlgebra ℂ (ℕ × ℕ) ≃ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  AddMonoidAlgebra.domCongr ℂ ℂ originalNativeMvExponentEquiv

/-- Every native single coefficient retains both monomial indices exactly. -/
theorem originalPositiveMvEquiv_single (n : ℕ × ℕ) (a : ℂ) :
    originalPositiveMvEquiv (AddMonoidAlgebra.single n a) =
      MvPolynomial.monomial (originalNativeMvExponentEquiv n) a :=
  AddMonoidAlgebra.domCongr_single _ _ _

/-- Arbitrary complex two-variable evaluation is exactly the original evaluation. -/
theorem originalPositiveMvEquiv_eval (Z W : ℂ) (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then Z else W) (originalPositiveMvEquiv p) =
      originalPositiveTorusEvaluation Z W p := by
  refine AddMonoidAlgebra.induction_linear p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro n a
    rw [originalPositiveMvEquiv_single, originalPositiveTorusEvaluation_single,
      MvPolynomial.eval_monomial]
    change a * ((Finsupp.single (0 : Fin 2) n.1 + Finsupp.single 1 n.2).prod
      (fun i e => (if i = 0 then Z else W) ^ e)) = a * (Z ^ n.1 * W ^ n.2)
    rw [Finsupp.prod_add_index] <;> simp [pow_add]

/-- EVERY two-variable complex point is covered by the actual original coordinate evaluation. -/
theorem originalPositiveMvEquiv_aeval (x : Fin 2 → ℂ) (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    MvPolynomial.aeval x (originalPositiveMvEquiv p) = originalPositiveTorusEvaluation (x 0) (x 1) p := by
  have hx : (fun i : Fin 2 => if i = 0 then x 0 else x 1) = x := by
    funext i
    fin_cases i <;> simp
  change MvPolynomial.eval x (originalPositiveMvEquiv p) = _
  simpa only [hx] using originalPositiveMvEquiv_eval (x 0) (x 1) p

end
end MeyerGeneralProblem.StrongParity
