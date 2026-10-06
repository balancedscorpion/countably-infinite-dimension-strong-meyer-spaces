module

public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-! Executable finite rational score minimization; no choice-defined minimizer. -/

namespace MeyerGeneralProblem.StrongParity

/-- The actual executable finite minimum using rational comparisons and a fallback. -/
def rationalFiniteMinimum (score : ℚ → ℚ) (candidates : List ℚ) (fallback : ℚ) : ℚ :=
  (candidates.argmin score).getD fallback

/-- A nonempty actual list supplies the selected value; the fallback is never used. -/
theorem rationalFiniteMinimum_some (score : ℚ → ℚ) {candidates : List ℚ}
    (hc : candidates ≠ []) (fallback : ℚ) :
    candidates.argmin score = some (rationalFiniteMinimum score candidates fallback) := by
  cases he : candidates.argmin score with
  | none => exact False.elim (hc (List.argmin_eq_none.mp he))
  | some q => simp [rationalFiniteMinimum, he]

theorem rationalFiniteMinimum_mem (score : ℚ → ℚ) {candidates : List ℚ}
    (hc : candidates ≠ []) (fallback : ℚ) :
    rationalFiniteMinimum score candidates fallback ∈ candidates :=
  List.argmin_mem (rationalFiniteMinimum_some score hc fallback)

/-- The selected ACTUAL rational score is at most every enumerated candidate score. -/
theorem rationalFiniteMinimum_score_le (score : ℚ → ℚ) {candidates : List ℚ}
    (hc : candidates ≠ []) (fallback : ℚ) {q : ℚ} (hq : q ∈ candidates) :
    score (rationalFiniteMinimum score candidates fallback) ≤ score q :=
  List.le_of_mem_argmin hq (rationalFiniteMinimum_some score hc fallback)

end MeyerGeneralProblem.StrongParity
