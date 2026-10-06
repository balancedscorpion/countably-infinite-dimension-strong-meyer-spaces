module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalUpperTube

@[expose] public section

/-! Literal finite slab coefficients on the integer lattice, with the original
quarter phase retained in every coefficient and in the actual entire evaluation. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem productNumeratorIntegerIndex_injective (s : ℕ) :
    Function.Injective (productNumeratorIntegerIndex s) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact_mod_cast (show ((p.val.1 : ℕ) : ℤ) = (q.val.1 : ℕ) from congrArg Prod.fst h)
  · exact_mod_cast (show ((p.val.2 : ℕ) : ℤ) = (q.val.2 : ℕ) from congrArg Prod.snd h)

/-- The full original slab as actual finite integer coefficients with its quarter phases. -/
def productSlabLaurentPolynomial (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  ∑ ij, AddMonoidAlgebra.single (productNumeratorIntegerIndex s ij)
    (r ij * complexUnitPhase (-1 / 4) ^ (ij.val.2 : ℕ))

theorem productSlabLaurentPolynomial_coefficient (s : ℕ)
    (r : productNumeratorIndex s → ℂ) (ij : productNumeratorIndex s) :
    (productSlabLaurentPolynomial s r).coeff (productNumeratorIntegerIndex s ij) =
      r ij * complexUnitPhase (-1 / 4) ^ (ij.val.2 : ℕ) := by
  classical
  simp only [productSlabLaurentPolynomial, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single ij]
  · exact Finsupp.single_eq_same
  · intro jk _ hjk
    exact Finsupp.single_eq_of_ne
      (fun h => hjk (productNumeratorIntegerIndex_injective s h.symm))
  · simp

theorem quarterPhase_pow (j : ℕ) :
    complexUnitPhase (-1 / 4) ^ j = unitPhase (-(j : ℝ) / 4) := by
  unfold complexUnitPhase unitPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem rankTwoLaurentEvaluation_slab (s : ℕ) (r : productNumeratorIndex s → ℂ) (z : ℂ) :
    rankTwoLaurentEvaluation z (productSlabLaurentPolynomial s r) =
      complexProductSlabNumerator s r z := by
  classical
  simp only [productSlabLaurentPolynomial, map_sum]
  change _ = ∑ ij : productNumeratorIndex s,
    r ij * complexUnitPhase z ^ (ij.val.1 : ℕ) *
      complexUnitPhase (beta * z - 1 / 4) ^ (ij.val.2 : ℕ)
  apply Finset.sum_congr rfl
  intro ij _
  simp only [rankTwoLaurentEvaluation, AddMonoidAlgebra.lift_single, smul_eq_mul,
    rankTwoEntireCharacter_apply, quarterPhase_pow]
  have hf : rankTwoFrequencyHom (productNumeratorIntegerIndex s ij) =
      positiveConeFrequency ((ij.val.1 : ℕ), (ij.val.2 : ℕ)) := by
    simp [rankTwoFrequencyHom_apply, productNumeratorIntegerIndex, positiveConeFrequency]
  rw [hf, mul_assoc]
  convert! congrArg (r ij * ·)
    (quarterFlow_phase_power ((ij.val.1 : ℕ), (ij.val.2 : ℕ)) z).symm using 1
  ring

end

end MeyerGeneralProblem.StrongParity
