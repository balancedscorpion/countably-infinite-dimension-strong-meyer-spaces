module

public import MeyerGeneralProblem.Cardinal.Strong.FaithfulLaurentFlow

@[expose] public section

/-! Finite Laurent multiplication of actual absolutely convergent tube series.
All integer translations and finite sums are discharged by HasSum reindexing. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem rankTwoEntireCharacter_add (z : ℂ) (m n : ℤ × ℤ) :
    rankTwoEntireCharacter z (Multiplicative.ofAdd (m + n)) =
      rankTwoEntireCharacter z (Multiplicative.ofAdd m) *
        rankTwoEntireCharacter z (Multiplicative.ofAdd n) :=
  (rankTwoEntireCharacter z).map_mul (Multiplicative.ofAdd m) (Multiplicative.ofAdd n)

/-- Multiplication by a finite original annihilator gives the actual
convolution coefficients on the WHOLE integer lattice. -/
theorem rankTwoLaurentConvolution_hasSum (p : AddMonoidAlgebra ℂ (ℤ × ℤ))
    (u : (ℤ × ℤ) → ℂ) (z A : ℂ)
    (h : HasSum (fun n => u n * rankTwoEntireCharacter z (Multiplicative.ofAdd n)) A) :
    HasSum (fun n => annihilatorArrayConvolution p.coeff u n *
      rankTwoEntireCharacter z (Multiplicative.ofAdd n))
      (rankTwoLaurentEvaluation z p * A) := by
  classical
  have hm (m : ℤ × ℤ) : HasSum
      (fun n => p.coeff m * u (n - m) * rankTwoEntireCharacter z (Multiplicative.ofAdd n))
      (p.coeff m * rankTwoEntireCharacter z (Multiplicative.ofAdd m) * A) := by
    apply (Equiv.addLeft m).hasSum_iff.mp
    convert! h.mul_left (p.coeff m * rankTwoEntireCharacter z (Multiplicative.ofAdd m)) using 1
    funext n
    simp only [Function.comp_def, Equiv.coe_addLeft, add_sub_cancel_left,
      rankTwoEntireCharacter_add]
    ring
  have hs := hasSum_sum (s := p.coeff.support) (fun m _ => hm m)
  rw [rankTwoLaurentEvaluation_eq_sum, Finset.sum_mul]
  convert! hs using 1
  funext n
  simp only [annihilatorArrayConvolution, Finset.sum_mul]

/-- An actual finite Laurent polynomial has its actual finite exponential
evaluation as its convergent whole-lattice sum. -/
theorem rankTwoLaurentEvaluation_hasSum (p : AddMonoidAlgebra ℂ (ℤ × ℤ)) (z : ℂ) :
    HasSum (fun n => p.coeff n * rankTwoEntireCharacter z (Multiplicative.ofAdd n))
      (rankTwoLaurentEvaluation z p) := by
  classical
  rw [rankTwoLaurentEvaluation_eq_sum]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  rw [Finsupp.notMem_support_iff.mp hn, zero_mul]

end

end MeyerGeneralProblem.StrongParity
