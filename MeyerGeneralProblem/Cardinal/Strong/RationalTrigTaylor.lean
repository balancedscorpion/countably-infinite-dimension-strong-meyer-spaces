module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-! Literal rational Taylor sums and errors against actual sine and cosine. -/

namespace MeyerGeneralProblem.StrongParity

/-- The executable rational sine derivative at zero, generated from parity. -/
def rationalSinCoefficient (i : ℕ) : ℚ :=
  if i % 2 = 0 then 0 else (-1 : ℚ) ^ (i / 2)

/-- The executable rational cosine derivative at zero, generated from parity. -/
def rationalCosCoefficient (i : ℕ) : ℚ :=
  if i % 2 = 0 then (-1 : ℚ) ^ (i / 2) else 0

/-- A literal finite rational sine Taylor sum with `N` terms. -/
def rationalSinTaylor (q : ℚ) (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, rationalSinCoefficient i * q ^ i / i.factorial

/-- A literal finite rational cosine Taylor sum with `N` terms. -/
def rationalCosTaylor (q : ℚ) (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, rationalCosCoefficient i * q ^ i / i.factorial

noncomputable section

theorem rationalSinCoefficient_cast (i : ℕ) :
    (rationalSinCoefficient i : ℝ) = iteratedDeriv i Real.sin 0 := by
  rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
  · simp [rationalSinCoefficient]
  · simp [rationalSinCoefficient, show (2 * k + 1) / 2 = k by omega]

theorem rationalCosCoefficient_cast (i : ℕ) :
    (rationalCosCoefficient i : ℝ) = iteratedDeriv i Real.cos 0 := by
  rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
  · simp [rationalCosCoefficient]
  · simp [rationalCosCoefficient]

theorem rationalSinTaylor_cast (q : ℚ) (N : ℕ) :
    (rationalSinTaylor q N : ℝ) =
      ∑ i ∈ Finset.range N, (rationalSinCoefficient i : ℝ) * (q : ℝ) ^ i / i.factorial := by
  simp [rationalSinTaylor]

theorem rationalCosTaylor_cast (q : ℚ) (N : ℕ) :
    (rationalCosTaylor q N : ℝ) =
      ∑ i ∈ Finset.range N, (rationalCosCoefficient i : ℝ) * (q : ℝ) ^ i / i.factorial := by
  simp [rationalCosTaylor]

theorem rationalSinTaylor_zero (N : ℕ) : rationalSinTaylor 0 N = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hz : i = 0
  · simp [hz, rationalSinCoefficient]
  · simp [zero_pow hz]

theorem rationalCosTaylor_zero {N : ℕ} (hN : 0 < N) : rationalCosTaylor 0 N = 1 := by
  unfold rationalCosTaylor
  rw [Finset.sum_eq_single 0]
  · simp [rationalCosCoefficient]
  · intro i hi hz
    simp [zero_pow hz]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hN))

/-- The rational sine sum is the ACTUAL Taylor polynomial, for both input signs. -/
theorem rationalSinTaylor_eq_taylor (q : ℚ) (hq : (q : ℝ) ≠ 0) (n : ℕ) :
    (rationalSinTaylor q (n + 1) : ℝ) =
      taylorWithinEval Real.sin n (Set.uIcc 0 (q : ℝ)) 0 q := by
  rw [rationalSinTaylor_cast, taylor_within_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hq))
    Real.contDiff_sin.contDiffAt (Set.left_mem_uIcc)]
  rw [← rationalSinCoefficient_cast]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The rational cosine sum is the ACTUAL Taylor polynomial, for both input signs. -/
theorem rationalCosTaylor_eq_taylor (q : ℚ) (hq : (q : ℝ) ≠ 0) (n : ℕ) :
    (rationalCosTaylor q (n + 1) : ℝ) =
      taylorWithinEval Real.cos n (Set.uIcc 0 (q : ℝ)) 0 q := by
  rw [rationalCosTaylor_cast, taylor_within_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hq))
    Real.contDiff_cos.contDiffAt (Set.left_mem_uIcc)]
  rw [← rationalCosCoefficient_cast]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- Certified actual sine remainder for EVERY signed rational input. -/
theorem rationalSinTaylor_error (q : ℚ) (n : ℕ) :
    |(rationalSinTaylor q (n + 1) : ℝ) - Real.sin (q : ℝ)| ≤
      |(q : ℝ)| ^ (n + 1) / (n + 1).factorial := by
  by_cases hq : (q : ℝ) = 0
  · have hqQ : q = 0 := by exact_mod_cast hq
    simp [hqQ, rationalSinTaylor_zero]
  rw [rationalSinTaylor_eq_taylor q hq n, abs_sub_comm]
  obtain ⟨x, hx, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (Ne.symm hq) (Real.contDiff_sin.contDiffOn : ContDiffOn ℝ (n + 1) Real.sin _)
  rw [he, abs_div, abs_mul, abs_pow, sub_zero, Nat.abs_cast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa using mul_le_mul_of_nonneg_right (Real.abs_iteratedDeriv_sin_le_one (n + 1) x)
    (pow_nonneg (abs_nonneg _) _)

/-- Certified actual cosine remainder for EVERY signed rational input. -/
theorem rationalCosTaylor_error (q : ℚ) (n : ℕ) :
    |(rationalCosTaylor q (n + 1) : ℝ) - Real.cos (q : ℝ)| ≤
      |(q : ℝ)| ^ (n + 1) / (n + 1).factorial := by
  by_cases hq : (q : ℝ) = 0
  · have hqQ : q = 0 := by exact_mod_cast hq
    simp [hqQ, rationalCosTaylor_zero (Nat.zero_lt_succ _)]
  rw [rationalCosTaylor_eq_taylor q hq n, abs_sub_comm]
  obtain ⟨x, hx, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (Ne.symm hq) (Real.contDiff_cos.contDiffOn : ContDiffOn ℝ (n + 1) Real.cos _)
  rw [he, abs_div, abs_mul, abs_pow, sub_zero, Nat.abs_cast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa using mul_le_mul_of_nonneg_right (Real.abs_iteratedDeriv_cos_le_one (n + 1) x)
    (pow_nonneg (abs_nonneg _) _)

end

end MeyerGeneralProblem.StrongParity
