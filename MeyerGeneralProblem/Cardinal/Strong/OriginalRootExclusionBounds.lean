module

public import MeyerGeneralProblem.Cardinal.Strong.FiniteRootParameterAvoidance

@[expose] public section

/-! Actual uniform rational-scale bounds protecting finite parameter exclusion intervals. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The actual fixed quartic dilation unit is bounded by two. -/
theorem parityDilationUnit_le_two : parityDilationUnit ≤ 2 := by
  have hc := parityDilationUnit_sq
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp := parityDilationUnit_pos
  nlinarith [sq_nonneg (Real.sqrt 2 - 2), sq_nonneg (parityDilationUnit - 2)]

/-- EVERY actual scaled root has the effective parameter Lipschitz bound 4*m. -/
theorem scaledCompactOriginalRoot_parameter_abs_sub_le (m : ℕ) (n : ℤ) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) (1 / 2)) (hb : b ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |scaledCompactOriginalRoot m n a - scaledCompactOriginalRoot m n b| ≤
      4 * (m : ℝ) * |a - b| := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hs : parityDilationUnit * (m : ℝ) ≤ 2 * (m : ℝ) :=
    mul_le_mul_of_nonneg_right parityDilationUnit_le_two hm
  have hp : 0 ≤ parityDilationUnit * (m : ℝ) := mul_nonneg parityDilationUnit_pos.le hm
  have hr := sheetRootLabel_parameter_abs_sub_le ha.1 ha.2 hb.1 hb.2 n
  rw [← compactOriginalRootLabel_eq n ha.1 ha.2, ← compactOriginalRootLabel_eq n hb.1 hb.2] at hr
  calc
    _ = (parityDilationUnit * (m : ℝ)) *
        |compactOriginalRootLabel n a - compactOriginalRootLabel n b| := by
      rw [scaledCompactOriginalRoot, scaledCompactOriginalRoot, ← mul_sub, abs_mul, abs_of_nonneg hp]
    _ ≤ (parityDilationUnit * (m : ℝ)) * (2 * |a - b|) := mul_le_mul_of_nonneg_left hr hp
    _ ≤ (2 * (m : ℝ)) * (2 * |a - b|) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring

/-- EVERY literal original exclusion residual has the same explicit 8*m parameter bound. -/
theorem OriginalRootExclusion.parameter_abs_sub_le (m : ℕ) (code : OriginalRootExclusion) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) (1 / 2)) (hb : b ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |code.residual m a - code.residual m b| ≤ 8 * (m : ℝ) * |a - b| := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hd : 0 ≤ (m : ℝ) * |a - b| := mul_nonneg hm (abs_nonneg _)
  cases code with
  | root n u v =>
      have h := scaledCompactOriginalRoot_parameter_abs_sub_le m n ha hb
      simp only [OriginalRootExclusion.residual, sub_sub_sub_cancel_right]
      nlinarith
  | fixed n y gamma =>
      have h := scaledCompactOriginalRoot_parameter_abs_sub_le m n ha hb
      simp only [OriginalRootExclusion.residual, sub_sub_sub_cancel_right]
      rw [show scaledCompactOriginalRoot m n a + y - (scaledCompactOriginalRoot m n b + y) =
        scaledCompactOriginalRoot m n a - scaledCompactOriginalRoot m n b by ring]
      nlinarith
  | difference n l u v =>
      by_cases hnl : n = l
      · simp only [OriginalRootExclusion.residual, ite_eq_left hnl, sub_self, abs_zero]
        positivity
      · have hn := scaledCompactOriginalRoot_parameter_abs_sub_le m n ha hb
        have hl := scaledCompactOriginalRoot_parameter_abs_sub_le m l ha hb
        simp only [OriginalRootExclusion.residual, ite_eq_right hnl, sub_sub_sub_cancel_right]
        calc
          _ = |(scaledCompactOriginalRoot m n a - scaledCompactOriginalRoot m n b) -
              (scaledCompactOriginalRoot m l a - scaledCompactOriginalRoot m l b)| := by
            congr 1
            ring
          _ ≤ |scaledCompactOriginalRoot m n a - scaledCompactOriginalRoot m n b| +
              |scaledCompactOriginalRoot m l a - scaledCompactOriginalRoot m l b| := abs_sub _ _
          _ ≤ 4 * (m : ℝ) * |a - b| + 4 * (m : ℝ) * |a - b| := add_le_add hn hl
          _ = _ := by ring
  | sum n l u v =>
      have hn := scaledCompactOriginalRoot_parameter_abs_sub_le m n ha hb
      have hl := scaledCompactOriginalRoot_parameter_abs_sub_le m l ha hb
      simp only [OriginalRootExclusion.residual, sub_sub_sub_cancel_right]
      calc
        _ = |(scaledCompactOriginalRoot m n a - scaledCompactOriginalRoot m n b) +
            (scaledCompactOriginalRoot m l a - scaledCompactOriginalRoot m l b)| := by
          congr 1
          ring
        _ ≤ |scaledCompactOriginalRoot m n a - scaledCompactOriginalRoot m n b| +
            |scaledCompactOriginalRoot m l a - scaledCompactOriginalRoot m l b| := abs_add_le _ _
        _ ≤ 4 * (m : ℝ) * |a - b| + 4 * (m : ℝ) * |a - b| := add_le_add hn hl
        _ = _ := by ring

/-- An actual center value supplies an explicit residual lower bound throughout a parameter interval. -/
theorem OriginalRootExclusion.residual_lower_bound (m : ℕ) (code : OriginalRootExclusion) {q a : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) (1 / 2)) (ha : a ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |code.residual m q| - 8 * (m : ℝ) * |a - q| ≤ |code.residual m a| := by
  have ht := abs_sub_abs_le_abs_sub (code.residual m q) (code.residual m a)
  have hl := code.parameter_abs_sub_le m hq ha
  rw [abs_sub_comm q a] at hl
  linarith

/-- A proved positive center margin protects ALL actual parameters in the stated interval. -/
theorem OriginalRootExclusion.ne_of_radius_margin (m : ℕ) (code : OriginalRootExclusion) {q a radius : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) (1 / 2)) (ha : a ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hd : |a - q| ≤ radius) (hmargin : 8 * (m : ℝ) * radius < |code.residual m q|) :
    code.residual m a ≠ 0 := by
  intro hz
  have hl := code.residual_lower_bound m hq ha
  have hd' := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 8 * (m : ℝ))
  rw [hz, abs_zero] at hl
  linarith

end

end MeyerGeneralProblem.StrongParity
