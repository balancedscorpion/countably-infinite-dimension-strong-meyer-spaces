module

public import MeyerGeneralProblem.Cardinal.Strong.RationalPhaseParameterInput
public import MeyerGeneralProblem.Cardinal.Strong.SheetRootLabels
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! Uniform continuity of the COMPLETE actual original compact root labels. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Every original labelled root is uniformly 2-Lipschitz in the compact parameter. -/
theorem sheetRootLabel_parameter_abs_sub_le {a b : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hb : 0 ≤ b) (hb2 : b ≤ 1 / 2) (n : ℤ) :
    |sheetRootLabel a ha (by linarith : a < 1) n -
      sheetRootLabel b hb (by linarith : b < 1) n| ≤ 2 * |a - b| := by
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  calc
    _ = |sheetRootLabel b hb hb1 n - sheetRootLabel a ha ha1 n| := abs_sub_comm _ _
    _ ≤ |sheetRootPhase a (sheetRootLabel b hb hb1 n) - (n : ℝ)| :=
      sheetRootLabel_residual_bound a ha ha1 n _
    _ = |sheetRootPhase a (sheetRootLabel b hb hb1 n) -
        sheetRootPhase b (sheetRootLabel b hb hb1 n)| := by rw [sheetRootLabel_phase]
    _ ≤ 2 * |a - b| := sheetRootPhase_parameter_abs_sub_le ha ha2 hb hb2 _

/-- The actual original compact-domain label, totalized by zero outside that domain. -/
def compactOriginalRootLabel (n : ℤ) (a : ℝ) : ℝ :=
  if h : 0 ≤ a ∧ a ≤ 1 / 2 then sheetRootLabel a h.1 (by linarith [h.2]) n else 0

theorem compactOriginalRootLabel_eq (n : ℤ) {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    compactOriginalRootLabel n a = sheetRootLabel a ha (by linarith : a < 1) n := by
  rw [compactOriginalRootLabel, dite_eq_left ⟨ha, ha2⟩]

theorem compactOriginalRootLabel_phase (n : ℤ) {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    sheetRootPhase a (compactOriginalRootLabel n a) = n := by
  rw [compactOriginalRootLabel_eq n ha ha2]
  exact sheetRootLabel_phase _ _ _ _

/-- The WHOLE compact-domain label satisfies the actual uniform Lipschitz bound. -/
theorem compactOriginalRootLabel_lipschitzOn (n : ℤ) :
    LipschitzOnWith 2 (compactOriginalRootLabel n) (Set.Icc (0 : ℝ) (1 / 2)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  simp only [Real.dist_eq, NNReal.coe_ofNat]
  rw [compactOriginalRootLabel_eq n ha.1 ha.2, compactOriginalRootLabel_eq n hb.1 hb.2]
  exact sheetRootLabel_parameter_abs_sub_le ha.1 ha.2 hb.1 hb.2 n

theorem compactOriginalRootLabel_continuousOn (n : ℤ) :
    ContinuousOn (compactOriginalRootLabel n) (Set.Icc (0 : ℝ) (1 / 2)) :=
  (compactOriginalRootLabel_lipschitzOn n).continuousOn

/-- Actual continuity includes the zero-parameter endpoint used by analytic exclusions. -/
theorem compactOriginalRootLabel_continuousWithinAt (n : ℤ) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ContinuousWithinAt (compactOriginalRootLabel n) (Set.Icc (0 : ℝ) (1 / 2)) a :=
  compactOriginalRootLabel_continuousOn n a ha

theorem compactOriginalRootLabel_zero (n : ℤ) :
    compactOriginalRootLabel n 0 = ((n : ℝ) + 1 / 4) / (1 + beta) := by
  rw [compactOriginalRootLabel_eq n (by norm_num) (by norm_num), sheetRootLabel_zero_parameter]

/-- Distinct actual compact parameters have distinct roots at every fixed label. -/
theorem compactOriginalRootLabel_injOn (n : ℤ) :
    Set.InjOn (compactOriginalRootLabel n) (Set.Icc (0 : ℝ) (1 / 2)) := by
  intro a ha b hb heq
  by_contra hab
  rw [compactOriginalRootLabel_eq n ha.1 ha.2, compactOriginalRootLabel_eq n hb.1 hb.2] at heq
  exact sheetRootLabel_parameters_ne ha.1 (by linarith [ha.2]) hb.1 (by linarith [hb.2]) hab n n heq

end

end MeyerGeneralProblem.StrongParity
