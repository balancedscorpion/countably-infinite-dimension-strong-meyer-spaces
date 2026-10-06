module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalPhaseAnalytic
public import MeyerGeneralProblem.Cardinal.Strong.RootParameterContinuity

@[expose] public section

/-! The actual analytic implicit branch at EVERY original compact labelled root. -/

namespace MeyerGeneralProblem.StrongParity

open Filter
open scoped Topology ContDiff

noncomputable section

/-- The actual original x derivative is an invertible scalar linear map. -/
theorem sheetRootPhase_partial_isInvertible {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (x : ℝ) :
    (fderiv ℝ (fun p : ℝ × ℝ => sheetRootPhase p.1 p.2) (a, x) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
  have hc := sheetRootPhase_contDiffAt a x (sheetLiftDenominator_pos ha ha1 _).ne'
  have hcomp := (hc.differentiableAt (by simp)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right a x)
  have hd := sheetRootPhase_hasDerivAt ha ha1 x
  have heq := hcomp.unique hd.hasFDerivAt
  rw [heq]
  have hn : 1 + beta * sheetLiftSpeed a (beta * x - 1 / 4) ≠ 0 := by
    have h := sheetRootPhase_deriv_gt_one ha ha1 x
    rw [hd.deriv] at h
    linarith
  exact ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hn), rfl⟩

/-- Analytic implicit inversion gives an ACTUAL branch and local uniqueness, also at a=0. -/
theorem sheetRootPhase_exists_analytic_branch {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (x : ℝ) :
    ∃ branch : ℝ → ℝ, AnalyticAt ℝ branch a ∧ branch a = x ∧
      (∀ᶠ b in 𝓝 a, sheetRootPhase b (branch b) = sheetRootPhase a x) ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (a, x),
        sheetRootPhase p.1 p.2 = sheetRootPhase a x ↔ branch p.1 = p.2) := by
  have hc := sheetRootPhase_contDiffAt a x (sheetLiftDenominator_pos ha ha1 _).ne'
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hi := sheetRootPhase_partial_isInvertible ha ha1 x
  refine ⟨hc.implicitFunction hn hi, (hc.contDiffAt_implicitFunction hn hi).analyticAt,
    hc.implicitFunction_apply_self hn hi, hc.eventually_apply_implicitFunction hn hi,
    hc.eventually_apply_eq_iff_implicitFunction hn hi⟩

/-- The analytic branch is matched to the COMPLETE original labels throughout the compact domain. -/
theorem compactOriginalRootLabel_exists_analytic_extension (n : ℤ) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ∃ branch : ℝ → ℝ, AnalyticAt ℝ branch a ∧ branch a = compactOriginalRootLabel n a ∧
      branch =ᶠ[𝓝[Set.Icc (0 : ℝ) (1 / 2)] a] compactOriginalRootLabel n := by
  obtain ⟨branch, hanalytic, hbase, _, hlocal⟩ :=
    sheetRootPhase_exists_analytic_branch ha.1 (by linarith [ha.2]) (compactOriginalRootLabel n a)
  have ht : Tendsto (fun b : ℝ => (b, compactOriginalRootLabel n b))
      (𝓝[Set.Icc (0 : ℝ) (1 / 2)] a) (𝓝 (a, compactOriginalRootLabel n a)) :=
    (continuousWithinAt_id.prodMk (compactOriginalRootLabel_continuousWithinAt n ha)).tendsto
  refine ⟨branch, hanalytic, hbase, ?_⟩
  filter_upwards [ht.eventually hlocal, self_mem_nhdsWithin] with b huniq hb
  apply huniq.mp
  rw [compactOriginalRootLabel_phase n hb.1 hb.2, compactOriginalRootLabel_phase n ha.1 ha.2]

/-- On the actual open compact range the original labels themselves are analytic. -/
theorem compactOriginalRootLabel_analyticAt (n : ℤ) {a : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    AnalyticAt ℝ (compactOriginalRootLabel n) a := by
  obtain ⟨branch, hanalytic, _, heq⟩ :=
    compactOriginalRootLabel_exists_analytic_extension n ⟨ha.1.le, ha.2.le⟩
  have hnhds : Set.Icc (0 : ℝ) (1 / 2) ∈ 𝓝 a := Icc_mem_nhds ha.1 ha.2
  rw [nhdsWithin_eq_nhds.mpr hnhds] at heq
  exact hanalytic.congr heq

/-- Analyticity on the connected original slot corridor, with every integer label included. -/
theorem compactOriginalRootLabel_analyticOnNhd (n : ℤ) :
    AnalyticOnNhd ℝ (compactOriginalRootLabel n) (Set.Ioo (0 : ℝ) (1 / 2)) :=
  fun _ ha => compactOriginalRootLabel_analyticAt n ha

end

end MeyerGeneralProblem.StrongParity
