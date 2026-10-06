module

public import MeyerGeneralProblem.Cardinal.Strong.ProductAnnihilator
public import Mathlib.Algebra.MonoidAlgebra.Support

@[expose] public section

/-! The actual product Laurent support lies in its original Newton box. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped Pointwise

theorem sheetLaurentPolynomial_support_box (a : ℝ) {n : ℤ × ℤ}
    (hn : n ∈ (sheetLaurentPolynomial a).coeff.support) :
    0 ≤ n.1 ∧ n.1 ≤ 1 ∧ 0 ≤ n.2 ∧ n.2 ≤ 1 := by
  classical
  have hn' := Finsupp.mem_support_iff.mp hn
  by_cases h0 : n = (0, 0)
  · subst n; norm_num
  by_cases h1 : n = (0, 1)
  · subst n; norm_num
  by_cases h2 : n = (1, 0)
  · subst n; norm_num
  by_cases h3 : n = (1, 1)
  · subst n; norm_num
  apply False.elim
  apply hn'
  simp [sheetLaurentPolynomial, h0, h1, h2, h3]

/-- All parameter choices have the same actual finite exponent box. -/
theorem finiteSheetLaurentProduct_support_box {ι : Type*} (E : Finset ι) (a : ι → ℝ)
    {n : ℤ × ℤ} (hn : n ∈ (∏ i ∈ E, sheetLaurentPolynomial (a i)).coeff.support) :
    0 ≤ n.1 ∧ n.1 ≤ E.card ∧ 0 ≤ n.2 ∧ n.2 ≤ E.card := by
  classical
  induction E using Finset.induction_on generalizing n with
  | empty =>
    have hn0 : n = (0, 0) := by
      convert! (show n = (0 : ℤ × ℤ) from by simpa using hn) using 1
    subst n
    norm_num
  | @insert i E hi ih =>
    rw [Finset.prod_insert hi] at hn
    obtain ⟨v, hv, w, hw, hsum⟩ := Finset.mem_add.mp
      (AddMonoidAlgebra.support_coeff_mul_subset _ _ hn)
    have hbv := sheetLaurentPolynomial_support_box (a i) hv
    have hbw := ih hw
    subst n
    simp only [Prod.fst_add, Prod.snd_add, Finset.card_insert_of_notMem hi, Nat.cast_add,
      Nat.cast_one]
    omega

theorem productLaurentCoefficients_support_box (s : ℕ) {n : ℤ × ℤ}
    (hn : n ∈ (productLaurentCoefficients s).support) :
    0 ≤ n.1 ∧ n.1 ≤ s ∧ 0 ≤ n.2 ∧ n.2 ≤ s := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    finiteSheetLaurentProduct_support_box Finset.univ (productSheetParameter s) hn

end

end MeyerGeneralProblem.StrongParity
