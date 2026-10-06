module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalRootParameterExclusions
public import Mathlib.Order.Filter.Finite

@[expose] public section

/-! A rational center avoiding EVERY equation in any actual finite PREFIX exclusion list. -/

namespace MeyerGeneralProblem.StrongParity

open Filter Set
open scoped Topology

noncomputable section

/-- Finite punctured-neighborhood exclusions contain a genuine rational safe center. -/
theorem finite_punctured_exclusions_rational_center {ι : Type*} [Finite ι]
    (values : ι → ℝ → ℝ) (levels : ι → ℝ) {u v : ℝ} (huv : u < v)
    (h : ∀ i, ∀ᶠ b in 𝓝[≠] u, values i b ≠ levels i) :
    ∃ q : ℚ, u < (q : ℝ) ∧ (q : ℝ) < v ∧ ∀ i, values i q ≠ levels i := by
  have hall : ∀ᶠ b in 𝓝[≠] u, ∀ i, values i b ≠ levels i := eventually_all.mpr h
  change {b : ℝ | ∀ i, values i b ≠ levels i} ∈ 𝓝[≠] u at hall
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhdsWithin_iff.mp hall
  have hmin : u < min v (u + epsilon) := lt_min huv (by linarith)
  obtain ⟨q, hq, hq'⟩ := exists_rat_btwn hmin
  refine ⟨q, hq, hq'.trans_le (min_le_left _ _), ?_⟩
  apply hball
  constructor
  · rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hq)]
    have hh := hq'.trans_le (min_le_right _ _)
    linarith
  · exact fun heq => (ne_of_gt hq) ((mem_singleton_iff.mp heq))

/-- The exact coarse-module value encoded by the two rational coefficients. -/
def rationalCoarseValue (u v : ℚ) : ℝ :=
  ((u : ℝ) + beta * (v : ℝ)) / parityDilationUnit

theorem rationalCoarseValue_mem (u v : ℚ) : rationalCoarseValue u v ∈ parityRationalCoarseModule :=
  ⟨u, v, rfl⟩

/-- Literal finite exclusion data from accepted PREFIX Section 2.
The difference of a label with itself is ignored, as the accepted contract requires. -/
inductive OriginalRootExclusion where
  /-- One original root avoids the encoded rational coarse value. -/
  | root (n : ℤ) (u v : ℚ)
  /-- A distinct-label original difference avoids the encoded rational coarse value. -/
  | difference (n l : ℤ) (u v : ℚ)
  /-- Any original sum, including a self-sum, avoids the encoded rational coarse value. -/
  | sum (n l : ℤ) (u v : ℚ)
  /-- An original root plus a previously fixed constant avoids a fixed real value. -/
  | fixed (n : ℤ) (y gamma : ℝ)

/-- The actual residual of one literal original root exclusion; invalid self-differences are one. -/
def OriginalRootExclusion.residual (m : ℕ) : OriginalRootExclusion → ℝ → ℝ
  | .root n u v, a => scaledCompactOriginalRoot m n a - rationalCoarseValue u v
  | .difference n l u v, a =>
    if n = l then 1 else scaledCompactOriginalRoot m n a - scaledCompactOriginalRoot m l a -
      rationalCoarseValue u v
  | .sum n l u v, a => scaledCompactOriginalRoot m n a + scaledCompactOriginalRoot m l a -
      rationalCoarseValue u v
  | .fixed n y gamma, a => scaledCompactOriginalRoot m n a + y - gamma

/-- EVERY encoded original equation has a proved local exclusion, with no analytic certificate input. -/
theorem OriginalRootExclusion.eventually_ne_zero (m : ℕ) (hm : 0 < m)
    (code : OriginalRootExclusion) {a : ℝ} (ha : a ∈ Ioo 0 (1 / 2)) :
    ∀ᶠ b in 𝓝[≠] a, code.residual m b ≠ 0 := by
  cases code with
  | root n u v =>
      simpa only [OriginalRootExclusion.residual, sub_ne_zero] using
        scaledCompactOriginalRoot_eventually_ne m hm n (gamma := rationalCoarseValue u v) ha
  | difference n l u v =>
      by_cases hnl : n = l
      · simp [OriginalRootExclusion.residual, hnl]
      · simpa only [OriginalRootExclusion.residual, ite_eq_right hnl, sub_ne_zero] using
          scaledCompactOriginalRoot_sub_eventually_ne m hm n l hnl (rationalCoarseValue_mem u v) ha
  | sum n l u v =>
      simpa only [OriginalRootExclusion.residual, sub_ne_zero] using
        scaledCompactOriginalRoot_add_eventually_ne m hm n l (rationalCoarseValue_mem u v) ha
  | fixed n y gamma =>
      simpa only [OriginalRootExclusion.residual, sub_ne_zero] using
        scaledCompactOriginalRoot_add_fixed_eventually_ne m hm n y (gamma := gamma) ha

/-- Every actual finite original exclusion family admits a rational center in EVERY assigned slot. -/
theorem actual_finite_root_exclusions_rational_center {ι : Type*} [Finite ι]
    (m : ℕ) (hm : 0 < m) (codes : ι → OriginalRootExclusion) {u v : ℝ}
    (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v) :
    ∃ q : ℚ, u < (q : ℝ) ∧ (q : ℝ) < v ∧ ∀ i, (codes i).residual m q ≠ 0 := by
  exact finite_punctured_exclusions_rational_center
    (fun i => (codes i).residual m) (fun _ => 0) huv
    (fun i => (codes i).eventually_ne_zero m hm ⟨hu, huv.trans_le hv⟩)

end

end MeyerGeneralProblem.StrongParity
