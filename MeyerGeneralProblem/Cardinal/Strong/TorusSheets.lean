module

public import MeyerGeneralProblem.Cardinal.Strong.ParityLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

/-!
# The actual sheet polynomial and its collision points

The algebraic sheets may intersect at both torus corners. The original
irrational quarter-phase flow misses both corners. No quantitative parity
lower bound or real/simple-root theorem is asserted here.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- `1 - a W + a Z - Z W`, with the same sign conventions as the source. -/
def sheetPolynomial (a Z W : ℂ) : ℂ := 1 - a * W + a * Z - Z * W

theorem sheetPolynomial_parameter_difference (a b Z W : ℂ) :
    sheetPolynomial b Z W - sheetPolynomial a Z W = (b - a) * (Z - W) := by
  unfold sheetPolynomial
  ring

/-- The two structural intersections are retained explicitly. -/
theorem sheetPolynomial_common_roots {a b Z W : ℂ} (hab : a ≠ b)
    (ha : sheetPolynomial a Z W = 0) (hb : sheetPolynomial b Z W = 0) :
    (Z = 1 ∧ W = 1) ∨ (Z = -1 ∧ W = -1) := by
  have hprod : (b - a) * (Z - W) = 0 := by
    rw [← sheetPolynomial_parameter_difference, ha, hb, sub_self]
  have hzw : Z = W := sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hab.symm))
  have hs : W ^ 2 = 1 := by
    rw [hzw] at ha
    dsimp [sheetPolynomial] at ha
    linear_combination -ha
  rcases sq_eq_one_iff.mp hs with h | h
  · exact Or.inl ⟨hzw.trans h, h⟩
  · exact Or.inr ⟨hzw.trans h, h⟩

/-- The original exponential phase, with period one. -/
def unitPhase (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

theorem unitPhase_square_eq_one_iff (t : ℝ) :
    unitPhase t ^ 2 = 1 ↔ ∃ k : ℤ, 2 * t = k := by
  have hs : unitPhase t ^ 2 = Complex.exp ((2 * Real.pi * (2 * t) : ℝ) * Complex.I) := by
    unfold unitPhase
    rw [pow_two, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hs, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hi := congrArg Complex.im hk
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_add, mul_one,
      add_zero, Complex.intCast_re, Complex.intCast_im] at hi
    have heq : (2 * Real.pi) * (2 * t) = (2 * Real.pi) * (k : ℝ) := by
      norm_num [Complex.mul_re] at hi
      simpa only [mul_comm] using hi
    exact mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) heq
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    ring

/-- Irrationality already excludes exact corner hits at the original
quarter phase; the stronger quantitative exclusion is a separate lemma. -/
theorem quarterFlow_misses_corners (x : ℝ) :
    ¬ (unitPhase x ^ 2 = 1 ∧ unitPhase (beta * x - 1 / 4) ^ 2 = 1) := by
  rintro ⟨hz, hw⟩
  obtain ⟨k, hk⟩ := (unitPhase_square_eq_one_iff x).mp hz
  obtain ⟨l, hl⟩ := (unitPhase_square_eq_one_iff (beta * x - 1 / 4)).mp hw
  by_cases hk0 : k = 0
  · rw [hk0, Int.cast_zero] at hk
    have hx : x = 0 := by linarith
    rw [hx] at hl
    have hlInt : 2 * l = -1 := by exact_mod_cast (show (2 : ℝ) * l = -1 by linarith)
    omega
  · apply beta_irrational.ne_rational (2 * l + 1) (2 * k)
    push_cast
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
      (Int.cast_ne_zero.mpr hk0))).mpr
    rw [← hk]
    nlinarith [hl]

/-- Distinct sheets have no common root on this real quarter-phase flow. -/
theorem quarterFlow_sheet_roots_disjoint {a b : ℂ} (hab : a ≠ b) (x : ℝ)
    (ha : sheetPolynomial a (unitPhase x) (unitPhase (beta * x - 1 / 4)) = 0) :
    sheetPolynomial b (unitPhase x) (unitPhase (beta * x - 1 / 4)) ≠ 0 := by
  intro hb
  have hc := sheetPolynomial_common_roots hab ha hb
  apply quarterFlow_misses_corners x
  rcases hc with ⟨hz, hw⟩ | ⟨hz, hw⟩ <;> rw [hz, hw] <;> norm_num

end

end MeyerGeneralProblem.StrongParity
