module

public import MeyerGeneralProblem.Cardinal.Strong.RootParameterContinuity
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

/-! The actual accepted zero-parameter coarse-module exclusion, using original beta. -/

namespace MeyerGeneralProblem.StrongParity

open Polynomial

noncomputable section

/-- The actual quartic dilation unit c=2^(1/4), represented by its positive square roots. -/
def parityDilationUnit : ℝ := Real.sqrt (Real.sqrt 2)

theorem parityDilationUnit_pos : 0 < parityDilationUnit := by
  unfold parityDilationUnit
  positivity

theorem parityDilationUnit_sq : parityDilationUnit ^ 2 = Real.sqrt 2 :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

/-- The accepted rational coarse module Gamma_Q=(Q+beta*Q)/c. -/
def parityRationalCoarseModule : Set ℝ :=
  {y | ∃ u v : ℚ, y = ((u : ℝ) + beta * (v : ℝ)) / parityDilationUnit}

/-- The ORIGINAL parity Liouville constant is transcendental over the rational field. -/
theorem beta_transcendental_rat : Transcendental ℚ beta := by
  intro h
  exact beta_liouville.transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr h)

/-- A nonzero scaled rational original base value cannot lie in the coarse module. -/
theorem scaled_rational_root_base_not_mem (m : ℕ) (hm : 0 < m) (q : ℚ) (hq : q ≠ 0) :
    parityDilationUnit * (m : ℝ) * (q : ℝ) / (1 + beta) ∉ parityRationalCoarseModule := by
  rintro ⟨u, v, h⟩
  have hc : parityDilationUnit ≠ 0 := parityDilationUnit_pos.ne'
  have hb : 1 + beta ≠ 0 := by linarith [beta_between_three_four]
  have he : Real.sqrt 2 * (m : ℝ) * (q : ℝ) =
      (v : ℝ) * beta ^ 2 + ((u : ℝ) + (v : ℝ)) * beta + (u : ℝ) := by
    have h' := (div_eq_div_iff hb hc).mp h
    rw [show (parityDilationUnit * (m : ℝ) * (q : ℝ)) * parityDilationUnit =
      parityDilationUnit ^ 2 * (m : ℝ) * (q : ℝ) by ring, parityDilationUnit_sq] at h'
    nlinarith [h']
  let P : ℚ[X] := C v * X ^ 2 + C (u + v) * X + C u
  let p : ℚ[X] := P ^ 2 - C (2 * (m : ℚ) ^ 2 * q ^ 2)
  have hP : aeval beta P = Real.sqrt 2 * (m : ℝ) * (q : ℝ) := by
    simp only [P, map_add, map_mul, map_pow, aeval_C, aeval_X]
    exact he.symm
  have hp : aeval beta p = 0 := by
    simp only [p, map_sub, map_pow, aeval_C, hP]
    push_cast
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    simp only [mul_pow, hs]
    norm_num
  have hz : p = 0 := (transcendental_iff.mp beta_transcendental_rat) p hp
  have hexp : p = C (v ^ 2) * X ^ 4 + C (2 * v * (u + v)) * X ^ 3 +
      C ((u + v) ^ 2 + 2 * u * v) * X ^ 2 + C (2 * u * (u + v)) * X +
      C (u ^ 2 - 2 * (m : ℚ) ^ 2 * q ^ 2) := by
    dsimp [p, P]
    simp only [map_add, map_mul, map_pow, map_sub, map_ofNat]
    ring
  have h4 : v ^ 2 = 0 := by
    have hh := congrArg (fun f : ℚ[X] => f.coeff 4) hz
    rw [hexp] at hh
    norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at hh
    simpa only [ite_true, ite_false, add_zero, zero_add, zero_sub, mul_zero, zero_mul] using hh
  have hv : v = 0 := sq_eq_zero_iff.mp h4
  have h2 : u ^ 2 = 0 := by
    have hh := congrArg (fun f : ℚ[X] => f.coeff 2) hz
    rw [hexp] at hh
    norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero, hv] at hh
    simpa only [ite_true, ite_false, add_zero, zero_add, zero_sub, mul_zero, zero_mul] using hh
  have hu : u = 0 := sq_eq_zero_iff.mp h2
  have h0 : -(2 * (m : ℚ) ^ 2 * q ^ 2) = 0 := by
    have hh := congrArg (fun f : ℚ[X] => f.coeff 0) hz
    rw [hexp] at hh
    norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero, hv, hu] at hh
    simpa only [ite_true, ite_false, add_zero, zero_add, zero_sub, mul_zero, zero_mul] using hh
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  exact (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hm'))
    (pow_ne_zero 2 hq))) h0

end

end MeyerGeneralProblem.StrongParity
