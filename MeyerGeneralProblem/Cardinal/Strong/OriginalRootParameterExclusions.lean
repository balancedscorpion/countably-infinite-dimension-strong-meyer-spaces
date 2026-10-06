module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalRootBaseExclusion
public import MeyerGeneralProblem.Cardinal.Strong.RootExclusionContinuation

@[expose] public section

/-! ALL literal scaled-root forbidden equations from accepted PREFIX Section 2. -/

namespace MeyerGeneralProblem.StrongParity

open Filter Set
open scoped Topology

noncomputable section

/-- The actual root at scale lambda=c*m on the original compact parameter corridor. -/
def scaledCompactOriginalRoot (m : ℕ) (n : ℤ) (a : ℝ) : ℝ :=
  (parityDilationUnit * (m : ℝ)) * compactOriginalRootLabel n a

/-- The fixed dilation is the positive actual quartic root of two. -/
theorem parityDilationUnit_fourth : parityDilationUnit ^ 4 = 2 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, parityDilationUnit_sq]
  exact Real.sq_sqrt (by norm_num)

theorem rational_int_add_quarter_ne_zero (n : ℤ) : (n : ℚ) + 1 / 4 ≠ 0 := by
  intro h
  have h' : (4 * n + 1 : ℤ) = 0 := by
    exact_mod_cast (show (4 : ℚ) * (n : ℚ) + 1 = 0 by linarith)
  omega

theorem rational_int_add_half_ne_zero (n : ℤ) : (n : ℚ) + 1 / 2 ≠ 0 := by
  intro h
  have h' : (2 * n + 1 : ℤ) = 0 := by
    exact_mod_cast (show (2 : ℚ) * (n : ℚ) + 1 = 0 by linarith)
  omega

/-- EVERY original scaled root base lies outside the actual rational coarse module. -/
theorem scaledCompactOriginalRoot_zero_not_mem (m : ℕ) (hm : 0 < m) (n : ℤ) :
    scaledCompactOriginalRoot m n 0 ∉ parityRationalCoarseModule := by
  have he : scaledCompactOriginalRoot m n 0 =
      parityDilationUnit * (m : ℝ) * (((n : ℚ) + 1 / 4 : ℚ) : ℝ) / (1 + beta) := by
    rw [scaledCompactOriginalRoot, compactOriginalRootLabel_zero]
    push_cast
    norm_num
    ring
  rw [he]
  exact scaled_rational_root_base_not_mem m hm _ (rational_int_add_quarter_ne_zero n)

/-- ALL distinct same-sheet original root differences have excluded actual base values. -/
theorem scaledCompactOriginalRoot_sub_zero_not_mem (m : ℕ) (hm : 0 < m) (n l : ℤ) (hnl : n ≠ l) :
    scaledCompactOriginalRoot m n 0 - scaledCompactOriginalRoot m l 0 ∉ parityRationalCoarseModule := by
  have he : scaledCompactOriginalRoot m n 0 - scaledCompactOriginalRoot m l 0 =
      parityDilationUnit * (m : ℝ) * (((n - l : ℤ) : ℚ) : ℝ) / (1 + beta) := by
    simp only [scaledCompactOriginalRoot, compactOriginalRootLabel_zero]
    push_cast
    ring
  rw [he]
  apply scaled_rational_root_base_not_mem m hm
  exact_mod_cast sub_ne_zero.mpr hnl

/-- ALL same-sheet original root sums, including a root with itself, have excluded base values. -/
theorem scaledCompactOriginalRoot_add_zero_not_mem (m : ℕ) (hm : 0 < m) (n l : ℤ) :
    scaledCompactOriginalRoot m n 0 + scaledCompactOriginalRoot m l 0 ∉ parityRationalCoarseModule := by
  have he : scaledCompactOriginalRoot m n 0 + scaledCompactOriginalRoot m l 0 =
      parityDilationUnit * (m : ℝ) * ((((n + l : ℤ) : ℚ) + 1 / 2 : ℚ) : ℝ) / (1 + beta) := by
    simp only [scaledCompactOriginalRoot, compactOriginalRootLabel_zero]
    push_cast
    norm_num
    ring
  rw [he]
  exact scaled_rational_root_base_not_mem m hm _ (rational_int_add_half_ne_zero (n + l))

theorem scaledCompactOriginalRoot_analyticOnNhd (m : ℕ) (n : ℤ) :
    AnalyticOnNhd ℝ (scaledCompactOriginalRoot m n) (Ioo 0 (1 / 2)) :=
  fun _ ha => analyticAt_const.mul (compactOriginalRootLabel_analyticAt n ha)

theorem scaledCompactOriginalRoot_continuousWithinAt_zero (m : ℕ) (n : ℤ) :
    ContinuousWithinAt (scaledCompactOriginalRoot m n) (Icc 0 (1 / 2)) 0 :=
  continuousWithinAt_const.mul (compactOriginalRootLabel_continuousWithinAt n (by norm_num))

/-- Actual nonzero scaling preserves the COMPLETE compact root branch's injectivity. -/
theorem scaledCompactOriginalRoot_injOn (m : ℕ) (hm : 0 < m) (n : ℤ) :
    InjOn (scaledCompactOriginalRoot m n) (Icc 0 (1 / 2)) := by
  intro a ha b hb heq
  apply compactOriginalRootLabel_injOn n ha hb
  exact mul_left_cancel₀ (mul_ne_zero parityDilationUnit_pos.ne' (by exact_mod_cast hm.ne')) heq

/-- EVERY single scaled original root equation has isolated solutions at any real level. -/
theorem scaledCompactOriginalRoot_eventually_ne (m : ℕ) (hm : 0 < m) (n : ℤ) {gamma a : ℝ}
    (ha : a ∈ Ioo 0 (1 / 2)) :
    ∀ᶠ b in 𝓝[≠] a, scaledCompactOriginalRoot m n b ≠ gamma :=
  analytic_injOn_compact_eventually_ne (scaledCompactOriginalRoot_analyticOnNhd m n)
    (scaledCompactOriginalRoot_injOn m hm n) ha

/-- Every cross-sheet exclusion with a previously fixed root has isolated solutions. -/
theorem scaledCompactOriginalRoot_add_fixed_eventually_ne (m : ℕ) (hm : 0 < m) (n : ℤ)
    (y : ℝ) {gamma a : ℝ} (ha : a ∈ Ioo 0 (1 / 2)) :
    ∀ᶠ b in 𝓝[≠] a, scaledCompactOriginalRoot m n b + y ≠ gamma := by
  apply analytic_injOn_compact_eventually_ne
  · exact fun _ hx => (scaledCompactOriginalRoot_analyticOnNhd m n _ hx).add analyticAt_const
  · intro u hu v hv h
    exact scaledCompactOriginalRoot_injOn m hm n hu hv (add_right_cancel h)
  · exact ha

/-- ALL distinct same-sheet root differences have isolated solutions to every coarse-module equation. -/
theorem scaledCompactOriginalRoot_sub_eventually_ne (m : ℕ) (hm : 0 < m) (n l : ℤ) (hnl : n ≠ l)
    {gamma a : ℝ} (hgamma : gamma ∈ parityRationalCoarseModule) (ha : a ∈ Ioo 0 (1 / 2)) :
    ∀ᶠ b in 𝓝[≠] a,
      scaledCompactOriginalRoot m n b - scaledCompactOriginalRoot m l b ≠ gamma := by
  apply analytic_compact_eventually_ne
  · exact (scaledCompactOriginalRoot_analyticOnNhd m n).sub (scaledCompactOriginalRoot_analyticOnNhd m l)
  · exact (scaledCompactOriginalRoot_continuousWithinAt_zero m n).sub
      (scaledCompactOriginalRoot_continuousWithinAt_zero m l)
  · intro h
    exact scaledCompactOriginalRoot_sub_zero_not_mem m hm n l hnl (h ▸ hgamma)
  · exact ha

/-- ALL same-sheet sums, including self-sums, have isolated solutions to every coarse-module equation. -/
theorem scaledCompactOriginalRoot_add_eventually_ne (m : ℕ) (hm : 0 < m) (n l : ℤ)
    {gamma a : ℝ} (hgamma : gamma ∈ parityRationalCoarseModule) (ha : a ∈ Ioo 0 (1 / 2)) :
    ∀ᶠ b in 𝓝[≠] a,
      scaledCompactOriginalRoot m n b + scaledCompactOriginalRoot m l b ≠ gamma := by
  apply analytic_compact_eventually_ne
  · exact (scaledCompactOriginalRoot_analyticOnNhd m n).add (scaledCompactOriginalRoot_analyticOnNhd m l)
  · exact (scaledCompactOriginalRoot_continuousWithinAt_zero m n).add
      (scaledCompactOriginalRoot_continuousWithinAt_zero m l)
  · intro h
    exact scaledCompactOriginalRoot_add_zero_not_mem m hm n l (h ▸ hgamma)
  · exact ha

end

end MeyerGeneralProblem.StrongParity
