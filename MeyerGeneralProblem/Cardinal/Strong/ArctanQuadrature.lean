module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Exact endpoint quadrature and certified finite errors for the ACTUAL arctangent.
This supplies the analytic proof behind executable rational phase evaluation.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open MeasureTheory intervalIntegral

/-- The actual arctangent integrand on a scaled finite grid. -/
def arctanGridIntegrand (q : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  1 / (1 + (q / N * t) ^ 2)

/-- The finite left endpoint sum, with its actual grid spacing. -/
def arctanQuadratureLeft (q : ℝ) (N : ℕ) : ℝ :=
  q / N * ∑ i ∈ Finset.range N, arctanGridIntegrand q N i

/-- The finite right endpoint sum, with the same actual grid spacing. -/
def arctanQuadratureRight (q : ℝ) (N : ℕ) : ℝ :=
  q / N * ∑ i ∈ Finset.range N, arctanGridIntegrand q N ((i : ℝ) + 1)

theorem arctanGridIntegrand_antitone {q : ℝ} (hq : 0 ≤ q) (N : ℕ) :
    AntitoneOn (arctanGridIntegrand q N) (Set.Icc 0 (0 + (N : ℝ))) := by
  intro x hx y hy hxy
  have hc : 0 ≤ q / (N : ℝ) := div_nonneg hq (Nat.cast_nonneg N)
  have hcx := mul_nonneg hc hx.1
  have hcy := mul_nonneg hc hy.1
  have hscale := mul_le_mul_of_nonneg_left hxy hc
  dsimp [arctanGridIntegrand]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- Exact change of variables identifies the scaled integral with arctangent. -/
theorem arctanGridIntegrand_integral (q : ℝ) {N : ℕ} (hN : 0 < N) :
    q / N * (∫ t in (0 : ℝ)..(N : ℝ), arctanGridIntegrand q N t) = Real.arctan q := by
  have hc : q / (N : ℝ) * (N : ℝ) = q :=
    div_mul_cancel₀ q (Nat.cast_ne_zero.mpr hN.ne')
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => 1 / (1 + t ^ 2)) (a := 0) (b := (N : ℝ)) (q / N)
  simpa only [arctanGridIntegrand, smul_eq_mul, mul_zero, hc,
    integral_one_div_one_add_sq, Real.arctan_zero, sub_zero] using h

/-- The actual arctangent lies between the two finite endpoint sums. -/
theorem arctanQuadrature_bracket {q : ℝ} (hq : 0 ≤ q) {N : ℕ} (hN : 0 < N) :
    arctanQuadratureRight q N ≤ Real.arctan q ∧
      Real.arctan q ≤ arctanQuadratureLeft q N := by
  have hc : 0 ≤ q / (N : ℝ) := div_nonneg hq (Nat.cast_nonneg N)
  have hl := mul_le_mul_of_nonneg_left (arctanGridIntegrand_antitone hq N).sum_le_integral hc
  have hu := mul_le_mul_of_nonneg_left (arctanGridIntegrand_antitone hq N).integral_le_sum hc
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at hl hu
  rw [arctanGridIntegrand_integral q hN] at hl hu
  exact ⟨hl, hu⟩

/-- Finite telescoping gives the EXACT endpoint-sum error width. -/
theorem arctanQuadrature_width (q : ℝ) {N : ℕ} (hN : 0 < N) :
    arctanQuadratureLeft q N - arctanQuadratureRight q N =
      q / N * (1 - 1 / (1 + q ^ 2)) := by
  have hc : q / (N : ℝ) * (N : ℝ) = q :=
    div_mul_cancel₀ q (Nat.cast_ne_zero.mpr hN.ne')
  have h := Finset.sum_range_sub (fun i : ℕ => arctanGridIntegrand q N i) N
  rw [Finset.sum_sub_distrib] at h
  simp only [arctanGridIntegrand, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
    mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, div_one, hc] at h
  dsimp [arctanQuadratureLeft, arctanQuadratureRight, arctanGridIntegrand]
  linear_combination -(q / (N : ℝ)) * h

/-- Actual finite-sum error, rather than an assumed approximation certificate. -/
theorem arctanQuadratureLeft_error_nonneg {q : ℝ} (hq : 0 ≤ q) {N : ℕ} (hN : 0 < N) :
    |arctanQuadratureLeft q N - Real.arctan q| ≤ q / N := by
  have hbr := arctanQuadrature_bracket hq hN
  have hc : 0 ≤ q / (N : ℝ) := div_nonneg hq (Nat.cast_nonneg N)
  rw [abs_of_nonneg (sub_nonneg.mpr hbr.2)]
  calc
    _ ≤ arctanQuadratureLeft q N - arctanQuadratureRight q N := sub_le_sub_left hbr.1 _
    _ = q / N * (1 - 1 / (1 + q ^ 2)) := arctanQuadrature_width q hN
    _ ≤ q / N * 1 := mul_le_mul_of_nonneg_left (sub_le_self 1 (by positivity : 0 ≤ 1 / (1 + q ^ 2))) hc
    _ = _ := mul_one _

theorem arctanGridIntegrand_neg (q : ℝ) (N : ℕ) (t : ℝ) :
    arctanGridIntegrand (-q) N t = arctanGridIntegrand q N t := by
  simp [arctanGridIntegrand, neg_div, neg_mul]

theorem arctanQuadratureLeft_neg (q : ℝ) (N : ℕ) :
    arctanQuadratureLeft (-q) N = -arctanQuadratureLeft q N := by
  simp [arctanQuadratureLeft, neg_div, arctanGridIntegrand_neg]

/-- The error certificate covers BOTH signs and arbitrary actual real arguments. -/
theorem arctanQuadratureLeft_error (q : ℝ) {N : ℕ} (hN : 0 < N) :
    |arctanQuadratureLeft q N - Real.arctan q| ≤ |q| / N := by
  by_cases hq : 0 ≤ q
  · simpa only [abs_of_nonneg hq] using arctanQuadratureLeft_error_nonneg hq hN
  · have hn := arctanQuadratureLeft_error_nonneg (by linarith : 0 ≤ -q) hN
    rw [arctanQuadratureLeft_neg, Real.arctan_neg, neg_sub_neg, abs_sub_comm] at hn
    simpa only [abs_of_neg (lt_of_not_ge hq)] using hn

end

end MeyerGeneralProblem.StrongParity
