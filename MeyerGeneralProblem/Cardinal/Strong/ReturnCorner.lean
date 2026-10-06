module

public import MeyerGeneralProblem.Cardinal.Strong.ReturnBounds

@[expose] public section

/-! The actual arithmetic sheet returns approach the original corner
in both phases. Every literal finite numerator tends to its actual
corner value, giving the numerator lower bound needed for exclusion. -/

namespace MeyerGeneralProblem.StrongParity

open Filter
open scoped Topology

noncomputable section

/-- `R(1,1)` for the original complete finite Newton slab. -/
def productSlabCornerValue (s : ℕ) (r : productNumeratorIndex s → ℂ) : ℂ := ∑ ij, r ij

theorem privateSheetRoot_firstPhase_tendsto (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n => unitPhase (privateSheetRoot a ha n)) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => (privateSheetRoot_phase_bounds a ha n).1)
  simpa only [mul_zero] using
    (tendsto_const_nhds (x := 2 * Real.pi)).mul privateReturnError_abs_tendsto_zero

theorem privateSheetRoot_secondPhase_tendsto (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n => unitPhase (beta * privateSheetRoot a ha n - 1 / 4)) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => (privateSheetRoot_phase_bounds a ha n).2.1)
  simpa only [mul_zero] using
    (tendsto_const_nhds (x := 2 * Real.pi * (1 + beta))).mul privateReturnError_abs_tendsto_zero

/-- EVERY original slab numerator tends to its original corner value. -/
theorem productSlabNumerator_privateRoot_tendsto (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n => productSlabNumerator s r (privateSheetRoot a ha n)) atTop
      (𝓝 (productSlabCornerValue s r)) := by
  unfold productSlabNumerator productSlabCornerValue
  apply tendsto_finsetSum
  intro ij _
  simpa only [one_pow, mul_one] using
    ((tendsto_const_nhds (x := r ij)).mul
      ((privateSheetRoot_firstPhase_tendsto a ha).pow (ij.val.1 : ℕ))).mul
        ((privateSheetRoot_secondPhase_tendsto a ha).pow (ij.val.2 : ℕ))

/-- Nonzero corner value supplies an actual eventual numerator norm lower bound. -/
theorem productSlabNumerator_privateRoot_eventually_lower
    (s : ℕ) (r : productNumeratorIndex s → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hJ : productSlabCornerValue s r ≠ 0) :
    ∀ᶠ n in atTop, ‖productSlabCornerValue s r‖ / 2 ≤
      ‖productSlabNumerator s r (privateSheetRoot a ha n)‖ := by
  have hpos : 0 < ‖productSlabCornerValue s r‖ := norm_pos_iff.mpr hJ
  exact ((productSlabNumerator_privateRoot_tendsto s r a ha).norm).eventually_const_le
    (by linarith)

/-- The chosen actual root as a point of the COMPLETE finite-product carrier. -/
def privateProductSheetRoot (s : ℕ) (i : Fin s) (n : ℕ) : (productSheetCarrier s).subtype :=
  productSheetRootInclusion s i
    ⟨privateSheetRoot (productSheetParameter s i) (productSheetParameter_bounds s i).1.le n,
      privateSheetRoot_is_root _ _ n⟩

/-- Actual escape gives the cofinite carrier filter, without an injective
enumeration hypothesis or any assertion that selected roots exhaust the carrier. -/
theorem privateProductSheetRoot_tendsto_cofinite (s : ℕ) (i : Fin s) :
    Tendsto (privateProductSheetRoot s i) atTop cofinite := by
  change map (privateProductSheetRoot s i) atTop ≤ cofinite
  apply le_cofinite_iff_eventually_ne.mpr
  intro y
  change ∀ᶠ n in atTop, privateProductSheetRoot s i n ≠ y
  filter_upwards [(privateSheetRoot_abs_tendsto_atTop (productSheetParameter s i)
    (productSheetParameter_bounds s i).1.le).eventually_gt_atTop |(y : ℝ)|] with n hn
  intro heq
  have hval := congrArg (fun x : (productSheetCarrier s).subtype => |(x : ℝ)|) heq
  exact (ne_of_gt hn) hval

end

end MeyerGeneralProblem.StrongParity
