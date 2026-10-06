module

public import MeyerGeneralProblem.Cardinal.Strong.SheetFiniteTaylor

@[expose] public section

/-! Complete finite Taylor convolution. Every degree is computed by finite
ring operations; the formulas apply to the derivatives of actual analytic
functions, rather than to a supplied coefficient certificate. -/

namespace MeyerGeneralProblem.StrongParity

/-- The finite coefficient convolution of an entire finite family. -/
def finiteTaylorProduct {R : Type*} [CommRing R] :
    {s : ℕ} → (Fin s → ℕ → R) → ℕ → R
  | 0, _, n => if n = 0 then 1 else 0
  | s + 1, f, n => ∑ j ∈ Finset.range (n + 1),
      f 0 j * finiteTaylorProduct (fun i : Fin s => f i.succ) (n - j)

noncomputable section

theorem originalTaylorCoefficient_mul {f g : ℂ → ℂ} (n : ℕ)
    (hf : ContDiffAt ℂ n f 0) (hg : ContDiffAt ℂ n g 0) :
    originalTaylorCoefficient (fun W => f W * g W) n =
      ∑ i ∈ Finset.range (n + 1),
        originalTaylorCoefficient f i * originalTaylorCoefficient g (n - i) := by
  unfold originalTaylorCoefficient
  rw [iteratedDeriv_fun_mul hf hg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have hnf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hif : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hdf : ((n - i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - i)
  have hfac : (n.choose i : ℂ) * i.factorial * (n - i).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  field_simp
  linear_combination (iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0) * hfac

theorem originalTaylorCoefficient_sum {ι : Type*} (A : Finset ι)
    (f : ι → ℂ → ℂ) (n : ℕ) (hf : ∀ i ∈ A, ContDiffAt ℂ n (f i) 0) :
    originalTaylorCoefficient (fun W => ∑ i ∈ A, f i W) n =
      ∑ i ∈ A, originalTaylorCoefficient (f i) n := by
  simp only [originalTaylorCoefficient, iteratedDeriv_fun_sum hf, Finset.sum_div]

/-- The finite convolution equals the normalized derivative of the whole product. -/
theorem finiteTaylorProduct_eq_taylor {s : ℕ} (f : Fin s → ℂ → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0) (n : ℕ) :
    finiteTaylorProduct (fun i => originalTaylorCoefficient (f i)) n =
      originalTaylorCoefficient (fun W => ∏ i : Fin s, f i W) n := by
  induction s generalizing n with
  | zero =>
    simp only [finiteTaylorProduct, Finset.univ_eq_empty, Finset.prod_empty]
    by_cases hn : n = 0 <;> simp [originalTaylorCoefficient, iteratedDeriv_const, hn]
  | succ s ih =>
    have hfun : (fun W => ∏ i : Fin (s + 1), f i W) =
        (fun W => f 0 W * ∏ i : Fin s, f i.succ W) := by
      funext W
      exact Fin.prod_univ_succ (fun i => f i W)
    rw [hfun, originalTaylorCoefficient_mul n (hf 0).contDiffAt
      (by apply AnalyticAt.contDiffAt; fun_prop)]
    simp only [finiteTaylorProduct]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ih (fun i => f i.succ) (fun i => hf i.succ) (n - i)]

end

end MeyerGeneralProblem.StrongParity
