module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalPositiveMvPolynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

/-! Genuine finite polynomial partitions from an actual no-common-zero orbit.
The complex Nullstellensatz and exact original evaluation transport supply the
coefficients; no unit-ideal or partition premise is assumed. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- A family of genuine original polynomials with no common complex zero generates
a finite exact polynomial partition. This does not assert that two relatively
prime divisors are comaximal, or that their intersections are empty. -/
theorem originalPositivePolynomialOrbit_partition_of_no_common_zero {ι : Type*}
    (p : ι → AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hzero : ∀ Z W : ℂ, ∃ g, originalPositiveTorusEvaluation Z W (p g) ≠ 0) :
    ∃ s : Finset ι, ∃ w : ι → AddMonoidAlgebra ℂ (ℕ × ℕ), ∑ g ∈ s, w g * p g = 1 := by
  classical
  let I : Ideal (MvPolynomial (Fin 2) ℂ) := Ideal.span (Set.range (fun g => originalPositiveMvEquiv (p g)))
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
    obtain ⟨g, hg⟩ := hzero (x 0) (x 1)
    have hp : originalPositiveMvEquiv (p g) ∈ M := hIM (Ideal.mem_span_range_self)
    rw [hx] at hp
    have he := (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).mp hp
    rw [originalPositiveMvEquiv_aeval] at he
    exact hg he
  have h1 : (1 : MvPolynomial (Fin 2) ℂ) ∈ I := (Ideal.eq_top_iff_one I).mp hI
  obtain ⟨w, hw⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp h1
  refine ⟨w.support, (fun g => originalPositiveMvEquiv.symm (w g)), ?_⟩
  have h := congrArg originalPositiveMvEquiv.symm hw
  simpa only [Finsupp.sum, map_sum, map_mul, AlgEquiv.symm_apply_apply, map_one] using h

end
end MeyerGeneralProblem.StrongParity
