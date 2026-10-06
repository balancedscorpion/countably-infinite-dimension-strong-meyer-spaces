module

public import MeyerGeneralProblem.Cardinal.Strong.SheetLiftDerivative
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-! The explicit monotone equation for EVERY original native sheet root. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The literal real equation whose integer levels are original sheet roots. -/
def sheetRootPhase (a x : ℝ) : ℝ := x + sheetPhaseLift a (beta * x - 1 / 4)

theorem unitPhase_eq_one_iff (t : ℝ) : unitPhase t = 1 ↔ ∃ n : ℤ, t = n := by
  unfold unitPhase
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hi := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_add, mul_one,
      add_zero, Complex.intCast_re, Complex.intCast_im] at hi
    have heq : (2 * Real.pi) * t = (2 * Real.pi) * (n : ℝ) := by
      norm_num [Complex.mul_re] at hi
      simpa only [mul_comm] using hi
    exact mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) heq
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    push_cast
    ring

/-- Exact factorization on the ORIGINAL quarter-phase sheet flow. -/
theorem sheetFlow_eq_rootPhase {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (x : ℝ) :
    sheetFlow a x = (1 - (a : ℂ) * unitPhase (beta * x - 1 / 4)) *
      (1 - unitPhase (sheetRootPhase a x)) := by
  have h := sheetPhaseLift_unitPhase_mul ha ha1 (beta * x - 1 / 4)
  rw [sheetRootPhase, unitPhase_add]
  dsimp [sheetFlow, sheetPolynomial]
  linear_combination unitPhase x * h

theorem sheetFlow_eq_zero_iff_rootPhase {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (x : ℝ) :
    sheetFlow a x = 0 ↔ ∃ n : ℤ, sheetRootPhase a x = n := by
  have hd : 1 - (a : ℂ) * unitPhase (beta * x - 1 / 4) ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.mp h)
    simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ha, unitPhase_norm, mul_one] at hn
    linarith
  rw [sheetFlow_eq_rootPhase ha ha1, mul_eq_zero, or_iff_right hd, sub_eq_zero,
    eq_comm, unitPhase_eq_one_iff]

theorem sheetRootPhase_hasDerivAt {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (x : ℝ) :
    HasDerivAt (sheetRootPhase a)
      (1 + beta * sheetLiftSpeed a (beta * x - 1 / 4)) x := by
  have hi : HasDerivAt (fun y : ℝ => beta * y - 1 / 4) beta x := by
    simpa using ((hasDerivAt_id x).const_mul beta).sub_const (1 / 4)
  have h := (hasDerivAt_id x).add
    ((sheetPhaseLift_hasDerivAt ha ha1 (beta * x - 1 / 4)).scomp x hi)
  convert! h using 1

theorem sheetRootPhase_deriv_gt_one {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (x : ℝ) :
    1 < deriv (sheetRootPhase a) x := by
  rw [(sheetRootPhase_hasDerivAt ha ha1 x).deriv]
  have hb : 0 < beta := by linarith [beta_between_three_four]
  have hs := sheetLiftSpeed_pos ha ha1 (beta * x - 1 / 4)
  nlinarith

theorem sheetRootPhase_strictMono {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    StrictMono (sheetRootPhase a) :=
  strictMono_of_deriv_pos fun x => lt_trans (by norm_num) (sheetRootPhase_deriv_gt_one ha ha1 x)

theorem sheetRootPhase_continuous {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Continuous (sheetRootPhase a) :=
  continuous_iff_continuousAt.mpr fun x => (sheetRootPhase_hasDerivAt ha ha1 x).continuousAt

/-- The bounded deviation gives a finite bracket for every integer level. -/
theorem sheetRootPhase_sub_bounds (a x : ℝ) :
    -(1 / 2) < sheetRootPhase a x - ((1 + beta) * x - 1 / 4) ∧
      sheetRootPhase a x - ((1 + beta) * x - 1 / 4) < 1 / 2 := by
  have h := sheetPhaseLift_sub_bounds a (beta * x - 1 / 4)
  dsimp [sheetRootPhase]
  constructor <;> nlinarith [h.1, h.2]

/-- The derivative lower bound controls inversion WITHOUT an equality test. -/
theorem sheetRootPhase_sub_lower {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) {x y : ℝ}
    (hxy : x ≤ y) : y - x ≤ sheetRootPhase a y - sheetRootPhase a x := by
  have hd (t : ℝ) := (sheetRootPhase_hasDerivAt ha ha1 t).sub (hasDerivAt_id t)
  have hm : Monotone (fun t => sheetRootPhase a t - t) := by
    apply monotone_of_deriv_nonneg
    · exact fun t => (hd t).differentiableAt
    · intro t
      change 0 ≤ deriv (sheetRootPhase a - id) t
      rw [(hd t).deriv]
      have hs := sheetRootPhase_deriv_gt_one ha ha1 t
      rw [(sheetRootPhase_hasDerivAt ha ha1 t).deriv] at hs
      linarith
  have h := hm hxy
  linarith

theorem sheetRootPhase_abs_lower {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (x y : ℝ) :
    |x - y| ≤ |sheetRootPhase a x - sheetRootPhase a y| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr ((sheetRootPhase_strictMono ha ha1).monotone hxy))]
    linarith [sheetRootPhase_sub_lower ha ha1 hxy]
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr ((sheetRootPhase_strictMono ha ha1).monotone hyx))]
    exact sheetRootPhase_sub_lower ha ha1 hyx

end

end MeyerGeneralProblem.StrongParity
