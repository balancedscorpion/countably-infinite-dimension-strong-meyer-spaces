module

public import MeyerGeneralProblem.Cardinal.Strong.RationalRootIntervals
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-! The actual computed binary root names converge to EVERY original labelled root. -/

namespace MeyerGeneralProblem.StrongParity

open Filter
open scoped Topology

noncomputable section

/-- A proved binary error schedule gives actual convergence of the emitted rational values. -/
theorem rational_binary_name_tendsto {values : ℕ → ℚ} {r : ℝ}
    (he : ∀ p, |(values p : ℝ) - r| ≤ 1 / (2 : ℝ) ^ p) :
    Tendsto (fun p => (values p : ℝ)) atTop (𝓝 r) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero (g := fun p => 1 / (2 : ℝ) ^ p) (fun _ => dist_nonneg) ?_ ?_
  · intro p
    simpa only [Real.dist_eq] using he p
  · simpa only [one_div_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)

/-- The actual finite rational original root program converges to the actual unique root. -/
theorem rationalOriginalRootApprox_tendsto {a : ℚ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (n : ℤ) :
    Tendsto (fun p => (rationalOriginalRootApprox a n p : ℝ)) atTop
      (𝓝 (sheetRootLabel (a : ℝ) (by exact_mod_cast ha) (rationalCompactParameter_lt_one ha2) n)) :=
  rational_binary_name_tendsto (rationalOriginalRootApprox_error ha ha2 n)

/-- The actual named-parameter program converges to its actual original labelled root. -/
theorem rationalNamedOriginalRootApprox_tendsto (name : ℕ → ℚ) {a : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hname_range : ∀ m, 0 ≤ name m ∧ name m ≤ 1 / 2)
    (hname_error : ∀ m, |(name m : ℝ) - a| ≤ 1 / (2 : ℝ) ^ m) (n : ℤ) :
    Tendsto (fun p => (rationalNamedOriginalRootApprox name n p : ℝ)) atTop
      (𝓝 (sheetRootLabel a ha (by linarith : a < 1) n)) :=
  rational_binary_name_tendsto (rationalNamedOriginalRootApprox_error name ha ha2 hname_range hname_error n)

theorem rationalOriginalRootApprox_cauchySeq {a : ℚ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (n : ℤ) :
    CauchySeq (fun p => (rationalOriginalRootApprox a n p : ℝ)) :=
  (rationalOriginalRootApprox_tendsto ha ha2 n).cauchySeq

theorem rationalNamedOriginalRootApprox_cauchySeq (name : ℕ → ℚ) {a : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hname_range : ∀ m, 0 ≤ name m ∧ name m ≤ 1 / 2)
    (hname_error : ∀ m, |(name m : ℝ) - a| ≤ 1 / (2 : ℝ) ^ m) (n : ℤ) :
    CauchySeq (fun p => (rationalNamedOriginalRootApprox name n p : ℝ)) :=
  (rationalNamedOriginalRootApprox_tendsto name ha ha2 hname_range hname_error n).cauchySeq

end

end MeyerGeneralProblem.StrongParity
