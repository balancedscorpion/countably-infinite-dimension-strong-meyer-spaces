module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalSheetPrimePolynomial
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

/-! Constant-normalized actual sheets have precisely classified associates.
Unit phases preserve the positive real parameter, while the native support
detects the dilation. Relative primality means no common nonunit divisor;
no Bezout or disjoint-intersection assertion is made. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open Polynomial

/-- Positive native dilation makes the actual constant coefficient exactly one. -/
theorem originalPhasedPositiveSheetPolynomial_origin (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ρ σ : ℂ) :
    originalPositiveTorusEvaluation 0 0 (originalPhasedPositiveSheetPolynomial d a ρ σ) = 1 := by
  rw [originalPhasedPositiveSheetPolynomial_eval]
  simp [sheetPolynomial, zero_pow (Nat.ne_of_gt hd)]

/-- The literal coefficient on the Z axis detects the positive native dilation. -/
theorem originalPhasedPositiveSheetPolynomial_coeff_first (d n : ℕ) (hd : 0 < d)
    (hn : 0 < n) (a : ℝ) (ρ σ : ℂ) :
    (originalPhasedPositiveSheetPolynomial d a ρ σ).coeff (n, 0) =
      if n = d then (a : ℂ) * ρ else 0 := by
  simp [originalPhasedPositiveSheetPolynomial, Nat.ne_of_gt hd, Nat.ne_of_gt hn,
    Finsupp.single_apply, eq_comm]

/-- The literal coefficient on the W axis retains the exact second phase. -/
theorem originalPhasedPositiveSheetPolynomial_coeff_second (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ρ σ : ℂ) :
    (originalPhasedPositiveSheetPolynomial d a ρ σ).coeff (0, d) = -(a : ℂ) * σ := by
  simp [originalPhasedPositiveSheetPolynomial, Nat.ne_of_gt hd]

/-- Units in the actual two-variable coefficient algebra are complex constants. -/
theorem originalPositivePolynomial_unit_constant
    (u : (AddMonoidAlgebra ℂ (ℕ × ℕ))ˣ) :
    ∃ c : ℂ, c ≠ 0 ∧ (u : AddMonoidAlgebra ℂ (ℕ × ℕ)) = AddMonoidAlgebra.single (0, 0) c := by
  have hu := u.isUnit.map originalPositiveIteratedEquiv
  obtain ⟨q, hq, hqu⟩ := Polynomial.isUnit_iff.mp hu
  obtain ⟨c, hc, hcq⟩ := Polynomial.isUnit_iff.mp hq
  refine ⟨c, hc.ne_zero, originalPositiveIteratedEquiv.injective ?_⟩
  rw [← hqu, ← hcq, originalPositiveIteratedEquiv_single]
  simp

/-- Normalization at the actual origin removes every associate unit internally. -/
theorem originalPositivePolynomial_associated_eq_of_normalized
    (p q : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hp : originalPositiveTorusEvaluation 0 0 p = 1)
    (hq : originalPositiveTorusEvaluation 0 0 q = 1) (h : Associated p q) : p = q := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, _, hc⟩ := originalPositivePolynomial_unit_constant u
  have he := congrArg (originalPositiveTorusEvaluation 0 0) hu
  rw [map_mul, hp, hq, hc, originalPositiveTorusEvaluation_single] at he
  simp only [pow_zero, one_mul, mul_one] at he
  rw [hc, he] at hu
  change p * 1 = q at hu
  simpa using hu

/-- Equal genuine sheets have equal positive native dilations, detected by an actual coefficient. -/
theorem originalPhasedPositiveSheetPolynomial_eq_dilation (d e : ℕ) (hd : 0 < d)
    (he : 0 < e) (a b : ℝ) (ha : 0 < a) (ρ σ τ υ : ℂ) (hρ : ρ ≠ 0)
    (h : originalPhasedPositiveSheetPolynomial d a ρ σ =
      originalPhasedPositiveSheetPolynomial e b τ υ) : d = e := by
  have hc := congrArg (fun p : AddMonoidAlgebra ℂ (ℕ × ℕ) => p.coeff (d, 0)) h
  rw [originalPhasedPositiveSheetPolynomial_coeff_first d d hd hd,
    originalPhasedPositiveSheetPolynomial_coeff_first e d he hd] at hc
  simp only [ite_true] at hc
  by_contra hde
  rw [ite_eq_right_iff.mpr (fun h => (hde h).elim)] at hc
  exact (mul_ne_zero (by exact_mod_cast ne_of_gt ha) hρ) hc

/-- Equal unit-phase sheets have equal positive real parameters, hence identical phases. -/
theorem originalPhasedPositiveSheetPolynomial_eq_parameters (d : ℕ) (hd : 0 < d)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ρ σ τ υ : ℂ)
    (hρ : ‖ρ‖ = 1) (hτ : ‖τ‖ = 1)
    (h : originalPhasedPositiveSheetPolynomial d a ρ σ =
      originalPhasedPositiveSheetPolynomial d b τ υ) : a = b ∧ ρ = τ ∧ σ = υ := by
  have hc := congrArg (fun p : AddMonoidAlgebra ℂ (ℕ × ℕ) => p.coeff (d, 0)) h
  rw [originalPhasedPositiveSheetPolynomial_coeff_first d d hd hd,
    originalPhasedPositiveSheetPolynomial_coeff_first d d hd hd] at hc
  simp only [ite_true] at hc
  have hn := congrArg norm hc
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
    abs_of_pos hb, hρ, hτ, mul_one] at hn
  subst b
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hphase : ρ = τ := mul_left_cancel₀ ha0 hc
  have hs := congrArg (fun p : AddMonoidAlgebra ℂ (ℕ × ℕ) => p.coeff (0, d)) h
  rw [originalPhasedPositiveSheetPolynomial_coeff_second d hd,
    originalPhasedPositiveSheetPolynomial_coeff_second d hd] at hs
  exact ⟨rfl, hphase, mul_left_cancel₀ (neg_ne_zero.mpr ha0) hs⟩

/-- ALL associates among genuine positive unit-phase sheets are exactly identical data. -/
theorem originalPhasedPositiveSheetPolynomial_associated_iff (d e : ℕ) (hd : 0 < d)
    (he : 0 < e) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ρ σ τ υ : ℂ)
    (hρ : ‖ρ‖ = 1) (hτ : ‖τ‖ = 1) :
    Associated (originalPhasedPositiveSheetPolynomial d a ρ σ)
      (originalPhasedPositiveSheetPolynomial e b τ υ) ↔ d = e ∧ a = b ∧ ρ = τ ∧ σ = υ := by
  constructor
  · intro h
    have hρ0 : ρ ≠ 0 := by intro hz; simp [hz] at hρ
    have hp := originalPositivePolynomial_associated_eq_of_normalized _ _
      (originalPhasedPositiveSheetPolynomial_origin d hd a ρ σ)
      (originalPhasedPositiveSheetPolynomial_origin e he b τ υ) h
    have hde := originalPhasedPositiveSheetPolynomial_eq_dilation d e hd he a b ha ρ σ τ υ hρ0 hp
    subst e
    exact ⟨rfl, originalPhasedPositiveSheetPolynomial_eq_parameters d hd a b ha hb ρ σ τ υ hρ hτ hp⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact Associated.refl _

/-- Different actual native dilations give no common nonunit sheet divisor. -/
theorem originalPhasedPositiveSheetPolynomial_isRelPrime_of_dilation_ne
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hde : d ≠ e)
    (a b : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (ρ σ τ υ : ℂ) (hρ : ‖ρ‖ = 1) (hτ : ‖τ‖ = 1) (hσ : σ ≠ 0) (hυ : υ ≠ 0) :
    IsRelPrime (originalPhasedPositiveSheetPolynomial d a ρ σ)
      (originalPhasedPositiveSheetPolynomial e b τ υ) := by
  have hρ0 : ρ ≠ 0 := by intro hz; simp [hz] at hρ
  have hτ0 : τ ≠ 0 := by intro hz; simp [hz] at hτ
  have hp := originalPhasedPositiveSheetPolynomial_irreducible d hd a ha ρ σ hρ0 hσ
  have hq := originalPhasedPositiveSheetPolynomial_irreducible e he b hb τ υ hτ0 hυ
  apply hp.isRelPrime_iff_not_dvd.mpr
  intro h
  have hass := hp.associated_of_dvd hq h
  exact hde ((originalPhasedPositiveSheetPolynomial_associated_iff d e hd he a b ha.1 hb.1
    ρ σ τ υ hρ hτ).mp hass).1

end
end MeyerGeneralProblem.StrongParity
