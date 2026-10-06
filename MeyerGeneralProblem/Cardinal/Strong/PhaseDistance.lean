module

public import MeyerGeneralProblem.Cardinal.Strong.TorusSheets
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.Order.Round

@[expose] public section

/-!
# Quantitative inversion of the original unit phase

The chord distance on the unit circle controls the distance to the
nearest integer translate of any prescribed phase. These estimates use
the literal exponential phase of the parity carrier.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem unitPhase_norm (t : ℝ) : ‖unitPhase t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem unitPhase_add (s t : ℝ) : unitPhase (s + t) = unitPhase s * unitPhase t := by
  unfold unitPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem unitPhase_integer (j : ℤ) : unitPhase j = 1 := by
  unfold unitPhase
  rw [Complex.exp_eq_one_iff]
  refine ⟨j, ?_⟩
  push_cast
  ring

theorem unitPhase_sub_integer (t : ℝ) (j : ℤ) : unitPhase (t - j) = unitPhase t := by
  rw [sub_eq_add_neg, ← Int.cast_neg, unitPhase_add, unitPhase_integer, mul_one]

theorem unitPhase_difference_norm (t s : ℝ) :
    ‖unitPhase t - unitPhase s‖ = ‖unitPhase (t - s) - 1‖ := by
  have h : unitPhase t - unitPhase s = (unitPhase (t - s) - 1) * unitPhase s := by
    rw [sub_mul, one_mul, ← unitPhase_add, sub_add_cancel]
  rw [h, norm_mul, unitPhase_norm, mul_one]

/-- Jordan's inequality gives a uniform inverse bound within half a period. -/
theorem unitPhase_chord_lower {t : ℝ} (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖unitPhase t - 1‖ := by
  have hpi : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hpi
  have hs' : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    convert hs using 1
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  have hnorm : ‖unitPhase t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
    unfold unitPhase
    rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
    norm_num [show 2 * Real.pi * t / 2 = Real.pi * t by ring, Real.norm_eq_abs,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hnorm]
  linarith

/-- The nearest translate controls both chord error and rounding size. -/
theorem unitPhase_nearest_translate (t s : ℝ) :
    ∃ j : ℤ, |t - ((j : ℝ) + s)| ≤ ‖unitPhase t - unitPhase s‖ / 4 ∧
      |t - ((j : ℝ) + s)| ≤ 1 / 2 := by
  let j := round (t - s)
  have hround : |t - s - (j : ℝ)| ≤ 1 / 2 := abs_sub_round (t - s)
  have hchord := unitPhase_chord_lower hround
  rw [unitPhase_sub_integer, ← unitPhase_difference_norm] at hchord
  refine ⟨j, ?_, ?_⟩ <;> rw [show t - ((j : ℝ) + s) = t - s - j by ring]
  · linarith
  · exact hround

end

end MeyerGeneralProblem.StrongParity
