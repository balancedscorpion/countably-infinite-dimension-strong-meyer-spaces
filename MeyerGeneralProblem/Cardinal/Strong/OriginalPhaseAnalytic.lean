module

public import MeyerGeneralProblem.Cardinal.Strong.SheetRootPhase
public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section

/-! Analytic regularity of the LITERAL original parameter/root equation. -/

namespace MeyerGeneralProblem.StrongParity

open scoped ContDiff

noncomputable section

/-- The original two-variable equation is analytic-order smooth at every safe denominator. -/
theorem sheetRootPhase_contDiffAt (a x : ℝ)
    (hd : sheetLiftDenominator a (beta * x - 1 / 4) ≠ 0) :
    ContDiffAt ℝ ω (fun p : ℝ × ℝ => sheetRootPhase p.1 p.2) (a, x) := by
  have ht : ContDiffAt ℝ ω (fun p : ℝ × ℝ => beta * p.2 - 1 / 4) (a, x) := by fun_prop
  have hn : ContDiffAt ℝ ω
      (fun p : ℝ × ℝ => p.1 * Real.sin (2 * Real.pi * (beta * p.2 - 1 / 4))) (a, x) := by
    fun_prop
  have hd' : ContDiffAt ℝ ω
      (fun p : ℝ × ℝ => sheetLiftDenominator p.1 (beta * p.2 - 1 / 4)) (a, x) := by
    unfold sheetLiftDenominator
    fun_prop
  have htan := hn.div hd' hd
  have hatan := Real.contDiff_arctan.contDiffAt.comp (a, x) htan
  exact contDiffAt_snd.add (ht.add (hatan.div_const Real.pi))

/-- EVERY original sheet parameter has actual analytic equation regularity, including zero. -/
theorem sheetRootPhase_analyticAt {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (x : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => sheetRootPhase p.1 p.2) (a, x) :=
  (sheetRootPhase_contDiffAt a x (sheetLiftDenominator_pos ha ha1 _).ne').analyticAt

end

end MeyerGeneralProblem.StrongParity
