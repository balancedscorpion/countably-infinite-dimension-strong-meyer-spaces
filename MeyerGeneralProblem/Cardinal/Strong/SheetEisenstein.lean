module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.Tactic

@[expose] public section

/-! Irreducibility of the genuine native sheet with arbitrary nonzero phases.
The simple zero and primitive polynomial are proved internally, using a literal
Eisenstein prime in the coefficient polynomial ring. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open Polynomial

/-- The actual constant coefficient in the first native variable. -/
def originalSheetConstantCoefficient (d : ℕ) (a σ : ℂ) : ℂ[X] :=
  1 - C (a * σ) * X ^ d

/-- The actual leading coefficient in the first native variable. -/
def originalSheetLeadingCoefficient (d : ℕ) (a ρ σ : ℂ) : ℂ[X] :=
  C ρ * (C a - C σ * X ^ d)

/-- The native sheet as an iterated polynomial, with the second coordinate inside. -/
def originalSheetIteratedPolynomial (d : ℕ) (a ρ σ : ℂ) : Polynomial ℂ[X] :=
  C (originalSheetLeadingCoefficient d a ρ σ) * X ^ d +
    C (originalSheetConstantCoefficient d a σ)

/-- The two actual coefficients have a literal nonzero constant combination. -/
theorem originalSheetCoefficient_combination (d : ℕ) (a ρ σ : ℂ) :
    C a * originalSheetLeadingCoefficient d a ρ σ -
      C ρ * originalSheetConstantCoefficient d a σ = C (ρ * (a ^ 2 - 1)) := by
  simp only [originalSheetLeadingCoefficient, originalSheetConstantCoefficient,
    map_mul, map_sub, map_pow, map_one]
  ring

/-- All iterated coefficients are exactly the constant and native leading terms. -/
theorem originalSheetIteratedPolynomial_coeff (d n : ℕ) (a ρ σ : ℂ) :
    (originalSheetIteratedPolynomial d a ρ σ).coeff n =
      (if n = d then originalSheetLeadingCoefficient d a ρ σ else 0) +
      (if n = 0 then originalSheetConstantCoefficient d a σ else 0) := by
  simp [originalSheetIteratedPolynomial, coeff_C_mul, coeff_X_pow, coeff_C]

/-- Nonzero actual leading coefficient gives the true positive native degree. -/
theorem originalSheetIteratedPolynomial_natDegree (d : ℕ) (a ρ σ : ℂ)
    (hl : originalSheetLeadingCoefficient d a ρ σ ≠ 0) :
    (originalSheetIteratedPolynomial d a ρ σ).natDegree = d := by
  rw [originalSheetIteratedPolynomial, natDegree_add_C, natDegree_C_mul_X_pow d _ hl]

/-- The actual coefficients force primitive descent, without a primitive certificate. -/
theorem originalSheetIteratedPolynomial_isPrimitive (d : ℕ) (hd : 0 < d)
    (a ρ σ : ℂ) (ha : a ^ 2 ≠ 1) (hρ : ρ ≠ 0) :
    (originalSheetIteratedPolynomial d a ρ σ).IsPrimitive := by
  intro r hr
  have hc := (C_dvd_iff_dvd_coeff r _).mp hr 0
  have hl := (C_dvd_iff_dvd_coeff r _).mp hr d
  simp only [originalSheetIteratedPolynomial_coeff, Nat.ne_of_gt hd,
    Ne.symm (Nat.ne_of_gt hd), ite_false, ite_true, zero_add, add_zero] at hc hl
  have hcomb := (hl.mul_left (C a)).sub (hc.mul_left (C ρ))
  rw [originalSheetCoefficient_combination] at hcomb
  have hu : IsUnit (C (ρ * (a ^ 2 - 1)) : ℂ[X]) :=
    isUnit_C.mpr (mul_ne_zero hρ (sub_ne_zero.mpr ha)).isUnit
  exact isUnit_of_dvd_unit hcomb hu

/-- A polynomial divisible by a squared linear root has zero derivative there. -/
theorem originalSquaredRoot_derivative_zero (p : ℂ[X]) (w : ℂ)
    (h : (X - C w) ^ 2 ∣ p) : p.derivative.eval w = 0 := by
  obtain ⟨q, rfl⟩ := h
  simp [derivative_mul, derivative_pow]

/-- Every nonzero complex phase sheet is irreducible at every positive native dilation.
The root, Eisenstein prime, simple multiplicity and primitive descent are internal. -/
theorem originalSheetIteratedPolynomial_irreducible (d : ℕ) (hd : 0 < d)
    (a ρ σ : ℂ) (ha0 : a ≠ 0) (ha : a ^ 2 ≠ 1) (hρ : ρ ≠ 0) (hσ : σ ≠ 0) :
    Irreducible (originalSheetIteratedPolynomial d a ρ σ) := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (1 / (a * σ)) hd
  have has : a * σ ≠ 0 := mul_ne_zero ha0 hσ
  have hw0 : w ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.ne_of_gt hd)] at hw
    exact (div_ne_zero one_ne_zero has) hw.symm
  have hroot : (originalSheetConstantCoefficient d a σ).eval w = 0 := by
    simp only [originalSheetConstantCoefficient, eval_sub, eval_one, eval_mul,
      eval_C, eval_pow, eval_X, hw]
    field_simp
    ring
  have hderiv : (originalSheetConstantCoefficient d a σ).derivative.eval w ≠ 0 := by
    simp only [originalSheetConstantCoefficient, derivative_sub, derivative_one,
      derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow,
      zero_sub, eval_neg, eval_mul, eval_C, eval_X, eval_pow]
    exact neg_ne_zero.mpr (mul_ne_zero has (mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)) (pow_ne_zero _ hw0)))
  have hlroot : (originalSheetLeadingCoefficient d a ρ σ).eval w ≠ 0 := by
    intro hz
    have he := congrArg (eval w) (originalSheetCoefficient_combination d a ρ σ)
    simp only [eval_sub, eval_mul, eval_C, hz, hroot, mul_zero, sub_self] at he
    exact (mul_ne_zero hρ (sub_ne_zero.mpr ha)) he.symm
  have hl : originalSheetLeadingCoefficient d a ρ σ ≠ 0 := by
    intro hz
    apply hlroot
    rw [hz, eval_zero]
  let P : Ideal ℂ[X] := Ideal.span {X - C w}
  have hP : P.IsPrime := Ideal.isPrime_span_singleton_of_prime (prime_X_sub_C w)
  have hmem (p : ℂ[X]) : p ∈ P ↔ p.eval w = 0 := by
    rw [Ideal.mem_span_singleton, dvd_iff_isRoot, IsRoot]
  have hlead : (originalSheetIteratedPolynomial d a ρ σ).leadingCoeff =
      originalSheetLeadingCoefficient d a ρ σ := by
    rw [leadingCoeff, originalSheetIteratedPolynomial_natDegree d a ρ σ hl,
      originalSheetIteratedPolynomial_coeff]
    simp [Nat.ne_of_gt hd]
  have hf0 : originalSheetIteratedPolynomial d a ρ σ ≠ 0 := by
    intro hz
    have hn := originalSheetIteratedPolynomial_natDegree d a ρ σ hl
    rw [hz, natDegree_zero] at hn
    omega
  have hdeg : (originalSheetIteratedPolynomial d a ρ σ).degree = (d : WithBot ℕ) := by
    rw [degree_eq_natDegree hf0, originalSheetIteratedPolynomial_natDegree d a ρ σ hl]
  apply irreducible_of_eisenstein_criterion hP
  · rw [hlead, hmem]
    exact hlroot
  · intro n hn
    rw [hdeg] at hn
    have hnd : n ≠ d := by intro h; simp [h] at hn
    rw [originalSheetIteratedPolynomial_coeff]
    simp only [hnd, ite_false, zero_add]
    split_ifs
    · exact (hmem _).mpr hroot
    · exact P.zero_mem
  · rw [hdeg]
    exact_mod_cast hd
  · rw [originalSheetIteratedPolynomial_coeff]
    simp only [Ne.symm (Nat.ne_of_gt hd), ite_false, ite_true, zero_add]
    intro hc
    have hs : (X - C w) ^ 2 ∣ originalSheetConstantCoefficient d a σ := by
      simpa only [P, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hc
    exact hderiv (originalSquaredRoot_derivative_zero _ w hs)
  · exact originalSheetIteratedPolynomial_isPrimitive d hd a ρ σ ha hρ

end
end MeyerGeneralProblem.StrongParity
