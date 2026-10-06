module

public import MeyerGeneralProblem.Cardinal.Strong.RationalIntervalGrid
public import MeyerGeneralProblem.Cardinal.Strong.RationalFiniteMinimum
public import MeyerGeneralProblem.Cardinal.Strong.OriginalRootMagnitude
public import MeyerGeneralProblem.Cardinal.Strong.RationalPhaseParameterInput

@[expose] public section

/-! An actual finite rational search for EVERY original labelled root.
The abstract evaluator interface is discharged by the literal implemented
original equation below; no approximation certificate survives there.
-/

namespace MeyerGeneralProblem.StrongParity

/-- The executable rational residual used by the original finite search. -/
def rationalOriginalRootResidual (evaluate : ℚ → ℚ) (n : ℤ) (x : ℚ) : ℚ := |evaluate x - n|

/-- The complete executable finite grid and actual rational minimum search. -/
def rationalOriginalRootSearchWith (evaluate : ℚ → ℚ) (n : ℤ) (p : ℕ) : ℚ :=
  rationalFiniteMinimum (rationalOriginalRootResidual evaluate n)
    (rationalIntervalGrid (originalRootSearchRadius n) (2 ^ (p + 4)))
    (-(originalRootSearchRadius n : ℚ))

/-- The actual original-root approximation using the IMPLEMENTED equation evaluator. -/
def rationalOriginalRootApprox (a : ℚ) (n : ℤ) (p : ℕ) : ℚ :=
  rationalOriginalRootSearchWith (fun x => rationalSheetRootPhaseApprox a x (p + 4)) n p

noncomputable section

theorem rationalOriginalRootSearchWith_mem (evaluate : ℚ → ℚ) (n : ℤ) (p : ℕ) :
    rationalOriginalRootSearchWith evaluate n p ∈
      rationalIntervalGrid (originalRootSearchRadius n) (2 ^ (p + 4)) :=
  rationalFiniteMinimum_mem _ (rationalIntervalGrid_nonempty _ _) _

/-- The program really minimizes the computed rational residual on the COMPLETE grid. -/
theorem rationalOriginalRootSearchWith_residual_le (evaluate : ℚ → ℚ) (n : ℤ) (p : ℕ)
    {q : ℚ} (hq : q ∈ rationalIntervalGrid (originalRootSearchRadius n) (2 ^ (p + 4))) :
    |evaluate (rationalOriginalRootSearchWith evaluate n p) - (n : ℚ)| ≤ |evaluate q - (n : ℚ)| :=
  rationalFiniteMinimum_score_le (rationalOriginalRootResidual evaluate n)
    (rationalIntervalGrid_nonempty (originalRootSearchRadius n) (2 ^ (p + 4)))
    (-(originalRootSearchRadius n : ℚ)) hq

/-- Finite-grid correctness against the ACTUAL original equation; all search steps are proved. -/
theorem rationalOriginalRootSearchWith_error (evaluate : ℚ → ℚ) {a : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (n : ℤ) (p : ℕ)
    (he : ∀ q : ℚ, |(evaluate q : ℝ) - sheetRootPhase a q| ≤ 1 / (2 : ℝ) ^ (p + 4)) :
    |(rationalOriginalRootSearchWith evaluate n p : ℝ) -
      sheetRootLabel a ha (by linarith : a < 1) n| ≤ 1 / (2 : ℝ) ^ p := by
  have ha1 : a < 1 := by linarith
  let r := sheetRootLabel a ha ha1 n
  let winner := rationalOriginalRootSearchWith evaluate n p
  obtain ⟨q, hq, hqr⟩ := rationalIntervalGrid_near_real
    (originalRootSearchRadius n) (2 ^ (p + 4)) (by positivity)
    (sheetRootLabel_search_radius a ha ha1 n)
  have hqr' : |(q : ℝ) - r| ≤ 1 / (2 : ℝ) ^ (p + 4) := by exact_mod_cast hqr
  have hr : sheetRootPhase a r = n := sheetRootLabel_phase a ha ha1 n
  have hnear : |sheetRootPhase a q - (n : ℝ)| ≤ 13 / (2 : ℝ) ^ (p + 4) := by
    rw [← hr]
    apply (sheetRootPhase_compact_abs_sub_le ha ha2 _ _).trans
    have h := mul_le_mul_of_nonneg_left hqr' (by norm_num : (0 : ℝ) ≤ 13)
    simpa only [mul_one_div] using h
  have hcost : |(evaluate q : ℝ) - (n : ℝ)| ≤ 14 / (2 : ℝ) ^ (p + 4) := by
    calc
      _ ≤ |(evaluate q : ℝ) - sheetRootPhase a q| + |sheetRootPhase a q - (n : ℝ)| :=
        abs_sub_le _ _ _
      _ ≤ 1 / (2 : ℝ) ^ (p + 4) + 13 / (2 : ℝ) ^ (p + 4) := add_le_add (he q) hnear
      _ = _ := by ring
  have hmin : |(evaluate winner : ℝ) - (n : ℝ)| ≤ |(evaluate q : ℝ) - (n : ℝ)| := by
    exact_mod_cast rationalOriginalRootSearchWith_residual_le evaluate n p hq
  have hw : |sheetRootPhase a winner - (n : ℝ)| ≤ 15 / (2 : ℝ) ^ (p + 4) := by
    calc
      _ ≤ |sheetRootPhase a winner - (evaluate winner : ℝ)| + |(evaluate winner : ℝ) - (n : ℝ)| :=
        abs_sub_le _ _ _
      _ ≤ 1 / (2 : ℝ) ^ (p + 4) + 14 / (2 : ℝ) ^ (p + 4) := by
        exact add_le_add (by simpa only [abs_sub_comm] using he winner) (hmin.trans hcost)
      _ = _ := by ring
  apply (sheetRootLabel_residual_bound a ha ha1 n winner).trans (hw.trans _)
  apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (p + 4))
    (by positivity : 0 < (2 : ℝ) ^ p)).mpr
  rw [pow_add]
  norm_num
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) p]

/-- The rational compact upper bound gives the actual native sheet domain. -/
theorem rationalCompactParameter_lt_one {a : ℚ} (ha2 : a ≤ 1 / 2) : (a : ℝ) < 1 := by
  have h : (a : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast ha2
  norm_num at h
  linarith

/-- EVERY original compact-range root is actually computed with uniform binary error. -/
theorem rationalOriginalRootApprox_error {a : ℚ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (n : ℤ) (p : ℕ) :
    |(rationalOriginalRootApprox a n p : ℝ) -
      sheetRootLabel (a : ℝ) (by exact_mod_cast ha)
        (rationalCompactParameter_lt_one ha2) n| ≤ 1 / (2 : ℝ) ^ p := by
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha2R : (a : ℝ) ≤ 1 / 2 := by
    have h : (a : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast ha2
    norm_num at h
    exact h
  exact rationalOriginalRootSearchWith_error _ haR ha2R n p
    (fun q => rationalSheetRootPhaseApprox_error ha ha2 q (p + 4))

end

end MeyerGeneralProblem.StrongParity
