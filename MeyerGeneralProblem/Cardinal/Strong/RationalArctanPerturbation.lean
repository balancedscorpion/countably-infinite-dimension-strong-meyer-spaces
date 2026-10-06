module

public import MeyerGeneralProblem.Cardinal.Strong.RationalArctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Safe real-input composition for the executable rational arctangent evaluator. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Input approximation error is never amplified by the ACTUAL arctangent. -/
theorem arctan_abs_sub_le (x y : ℝ) : |Real.arctan x - Real.arctan y| ≤ |x - y| := by
  have hbound (z : ℝ) : ‖deriv Real.arctan z‖ ≤ (1 : ℝ) := by
    rw [Real.deriv_arctan, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg z]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Real.arctan) (s := Set.univ)
    (C := 1) (fun z _ => Real.differentiableAt_arctan z) (fun z _ => hbound z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using h

/-- The computed rational value remains certified for an approximated real input. -/
theorem rationalArctanApprox_real_error (q : ℚ) (p : ℕ) (x ε : ℝ)
    (hq : |(q : ℝ) - x| ≤ ε) :
    |(rationalArctanApprox q p : ℝ) - Real.arctan x| ≤ 1 / (2 : ℝ) ^ p + ε := by
  calc
    _ = |((rationalArctanApprox q p : ℝ) - Real.arctan (q : ℝ)) +
        (Real.arctan (q : ℝ) - Real.arctan x)| := by congr 1; ring
    _ ≤ |(rationalArctanApprox q p : ℝ) - Real.arctan (q : ℝ)| +
        |Real.arctan (q : ℝ) - Real.arctan x| := abs_add_le _ _
    _ ≤ 1 / (2 : ℝ) ^ p + |(q : ℝ) - x| :=
      add_le_add (rationalArctanApprox_error q p) (arctan_abs_sub_le _ _)
    _ ≤ _ := add_le_add_right hq _

end

end MeyerGeneralProblem.StrongParity
