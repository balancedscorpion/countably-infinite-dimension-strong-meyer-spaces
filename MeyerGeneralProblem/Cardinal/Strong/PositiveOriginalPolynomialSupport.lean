module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixArray
public import Mathlib.Algebra.MonoidAlgebra.Support

@[expose] public section
/-! Whole native boxes for the ACTUAL complete mixed original polynomial.
All monomial collisions are retained; the actual sum of sheet counts times
coordinate dilations supplies the common bidegree internally. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped Pointwise

/-- Every literal positive sheet monomial lies in its internally known native degree box. -/
theorem originalPositiveSheetPolynomial_support_box (d : ℕ) (a : ℝ) {n : ℕ × ℕ}
    (hn : n ∈ (originalPositiveSheetPolynomial d a).coeff.support) : n.1 ≤ d ∧ n.2 ≤ d := by
  classical
  have hn' := Finsupp.mem_support_iff.mp hn
  by_cases h0 : n = (0, 0)
  · subst n; simp
  by_cases h1 : n = (0, d)
  · subst n; simp
  by_cases h2 : n = (d, 0)
  · subst n; simp
  by_cases h3 : n = (d, d)
  · subst n; simp
  apply False.elim
  apply hn'
  simp [originalPositiveSheetPolynomial, h0, h1, h2, h3]

/-- Genuine polynomial multiplication sums all collisions within the sum of the native boxes. -/
theorem finiteOriginalPositivePolynomialProduct_support_box {ι : Type*} (E : Finset ι)
    (q : ι → AddMonoidAlgebra ℂ (ℕ × ℕ)) (b : ι → ℕ)
    (hq : ∀ i ∈ E, ∀ n ∈ (q i).coeff.support, n.1 ≤ b i ∧ n.2 ≤ b i)
    {n : ℕ × ℕ} (hn : n ∈ (∏ i ∈ E, q i).coeff.support) :
    n.1 ≤ ∑ i ∈ E, b i ∧ n.2 ≤ ∑ i ∈ E, b i := by
  classical
  induction E using Finset.induction_on generalizing n with
  | empty =>
    have hn0 : n = (0 : ℕ × ℕ) := by simpa using hn
    subst n
    simp
  | @insert i E hi ih =>
    rw [Finset.prod_insert hi] at hn
    obtain ⟨v, hv, w, hw, hsum⟩ := Finset.mem_add.mp
      (AddMonoidAlgebra.support_coeff_mul_subset _ _ hn)
    have hbv := hq i (Finset.mem_insert_self i E) v hv
    have hbw := ih (fun j hj => hq j (Finset.mem_insert_of_mem hj)) hw
    subst n
    simp only [Prod.fst_add, Prod.snd_add, Finset.sum_insert hi]
    omega

/-- Actual mixed degree: ALL sheets of EVERY block at their common coordinate dilation. -/
def originalScheduledPrefixPolynomialDegree (bound : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i : Fin k, originalReflectedOrderSchedule bound i.val * originalScheduledPrefixCoordinateDilation bound k i

/-- The ACTUAL complete mixed original polynomial has its proved common native box. -/
theorem originalScheduledPrefixPolynomial_support_box (bound : ℕ → ℕ) (k : ℕ) {n : ℕ × ℕ}
    (hn : n ∈ (originalScheduledPrefixPolynomial bound k).coeff.support) :
    n.1 ≤ originalScheduledPrefixPolynomialDegree bound k ∧ n.2 ≤ originalScheduledPrefixPolynomialDegree bound k := by
  apply finiteOriginalPositivePolynomialProduct_support_box Finset.univ
    (fun i : Fin k => ∏ j : Fin (originalReflectedOrderSchedule bound i.val),
      originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
        ((originalScheduledParameterBlock bound i.val).parameter j))
    (fun i => originalReflectedOrderSchedule bound i.val * originalScheduledPrefixCoordinateDilation bound k i) _ hn
  intro i _ m hm
  have h := finiteOriginalPositivePolynomialProduct_support_box Finset.univ
    (fun j : Fin (originalReflectedOrderSchedule bound i.val) =>
      originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
        ((originalScheduledParameterBlock bound i.val).parameter j))
    (fun _ => originalScheduledPrefixCoordinateDilation bound k i)
    (fun j _ n hn => originalPositiveSheetPolynomial_support_box _ _ hn) hm
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using h
end
end MeyerGeneralProblem.StrongParity
