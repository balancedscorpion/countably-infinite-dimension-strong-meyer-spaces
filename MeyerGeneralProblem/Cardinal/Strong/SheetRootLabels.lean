module

public import MeyerGeneralProblem.Cardinal.Strong.SheetRootPhase

@[expose] public section

/-! Complete integer labels, explicit brackets and residual error for ORIGINAL roots.
Unique-root choice is used only to name the proved branch. This module does not
claim Type-2 computation or a certified determinant-search implementation.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The explicit lower bracket endpoint for the original integer root level. -/
def sheetRootBracketLower (n : ℤ) : ℝ := ((n : ℝ) + 1 / 4 - 1 / 2) / (1 + beta)

/-- The explicit upper bracket endpoint for the original integer root level. -/
def sheetRootBracketUpper (n : ℤ) : ℝ := ((n : ℝ) + 1 / 4 + 1 / 2) / (1 + beta)

theorem sheetRootBracket_order (n : ℤ) : sheetRootBracketLower n < sheetRootBracketUpper n := by
  have hb : 0 < 1 + beta := by linarith [beta_between_three_four]
  dsimp [sheetRootBracketLower, sheetRootBracketUpper]
  rw [div_lt_div_iff_of_pos_right hb]
  linarith

theorem sheetRootPhase_bracket (a : ℝ) (n : ℤ) :
    sheetRootPhase a (sheetRootBracketLower n) < n ∧
      (n : ℝ) < sheetRootPhase a (sheetRootBracketUpper n) := by
  have hb : (1 + beta) ≠ 0 := by linarith [beta_between_three_four]
  have hl : (1 + beta) * sheetRootBracketLower n - 1 / 4 = (n : ℝ) - 1 / 2 := by
    dsimp [sheetRootBracketLower]
    field_simp
    ring
  have hu : (1 + beta) * sheetRootBracketUpper n - 1 / 4 = (n : ℝ) + 1 / 2 := by
    dsimp [sheetRootBracketUpper]
    field_simp
    ring
  have hlow := (sheetRootPhase_sub_bounds a (sheetRootBracketLower n)).2
  have hhigh := (sheetRootPhase_sub_bounds a (sheetRootBracketUpper n)).1
  rw [hl] at hlow
  rw [hu] at hhigh
  constructor <;> linarith

/-- EVERY integer level has exactly one original root, inside the finite bracket. -/
theorem sheetRootPhase_existsUnique {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (n : ℤ) :
    ∃! x : ℝ, sheetRootPhase a x = n := by
  have hbr := sheetRootPhase_bracket a n
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (sheetRootBracket_order n).le
    (sheetRootPhase_continuous ha ha1).continuousOn ⟨hbr.1.le, hbr.2.le⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact (sheetRootPhase_strictMono ha ha1).injective (hy.trans hx.symm)

/-- The unique actual original root of integer level `n`, named by unique choice. -/
def sheetRootLabel (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℤ) : ℝ :=
  Classical.choose (sheetRootPhase_existsUnique ha ha1 n).exists

theorem sheetRootLabel_phase (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℤ) :
    sheetRootPhase a (sheetRootLabel a ha ha1 n) = n :=
  Classical.choose_spec (sheetRootPhase_existsUnique ha ha1 n).exists

theorem sheetRootLabel_is_root (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℤ) :
    sheetFlow a (sheetRootLabel a ha ha1 n) = 0 :=
  (sheetFlow_eq_zero_iff_rootPhase ha ha1 _).mpr ⟨n, sheetRootLabel_phase a ha ha1 n⟩

/-- The labels exhaust the WHOLE original sheet zero set. -/
theorem sheetFlow_eq_zero_iff_label {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (x : ℝ) :
    sheetFlow a x = 0 ↔ ∃ n : ℤ, sheetRootLabel a ha ha1 n = x := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := (sheetFlow_eq_zero_iff_rootPhase ha ha1 x).mp hx
    exact ⟨n, (sheetRootPhase_strictMono ha ha1).injective
      ((sheetRootLabel_phase a ha ha1 n).trans hn.symm)⟩
  · rintro ⟨n, rfl⟩
    exact sheetRootLabel_is_root a ha ha1 n

theorem sheetRootLabel_strictMono (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    StrictMono (sheetRootLabel a ha ha1) := by
  intro m n hmn
  apply (sheetRootPhase_strictMono ha ha1).lt_iff_lt.mp
  rw [sheetRootLabel_phase, sheetRootLabel_phase]
  exact_mod_cast hmn

theorem sheetRootLabel_in_bracket (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℤ) :
    sheetRootBracketLower n < sheetRootLabel a ha ha1 n ∧
      sheetRootLabel a ha ha1 n < sheetRootBracketUpper n := by
  have hbr := sheetRootPhase_bracket a n
  constructor
  · apply (sheetRootPhase_strictMono ha ha1).lt_iff_lt.mp
    rw [sheetRootLabel_phase]
    exact hbr.1
  · apply (sheetRootPhase_strictMono ha ha1).lt_iff_lt.mp
    rw [sheetRootLabel_phase]
    exact hbr.2

/-- Certified function-value error bounds ORIGINAL root-location error. -/
theorem sheetRootLabel_residual_bound (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℤ) (x : ℝ) :
    |x - sheetRootLabel a ha ha1 n| ≤ |sheetRootPhase a x - n| := by
  simpa only [sheetRootLabel_phase] using
    sheetRootPhase_abs_lower ha ha1 x (sheetRootLabel a ha ha1 n)

theorem sheetRootPhase_zero_parameter (x : ℝ) :
    sheetRootPhase 0 x = (1 + beta) * x - 1 / 4 := by
  rw [sheetRootPhase, sheetPhaseLift_zero_parameter]
  ring

/-- The literal branch base point from the accepted construction. -/
theorem sheetRootLabel_zero_parameter (n : ℤ) :
    sheetRootLabel 0 (by norm_num) (by norm_num) n = ((n : ℝ) + 1 / 4) / (1 + beta) := by
  have h := sheetRootLabel_phase 0 (by norm_num) (by norm_num) n
  rw [sheetRootPhase_zero_parameter] at h
  apply (eq_div_iff (by linarith [beta_between_three_four] : (1 + beta) ≠ 0)).mpr
  nlinarith

/-- Distinct actual parameters give different roots for ANY two labels. -/
theorem sheetRootLabel_parameters_ne {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hb : 0 ≤ b) (hb1 : b < 1) (hab : a ≠ b) (n m : ℤ) :
    sheetRootLabel a ha ha1 n ≠ sheetRootLabel b hb hb1 m := by
  intro heq
  have hA := sheetRootLabel_is_root a ha ha1 n
  have hB := sheetRootLabel_is_root b hb hb1 m
  rw [← heq] at hB
  exact quarterFlow_sheet_roots_disjoint (Complex.ofReal_injective.ne hab) _ hA hB

end

end MeyerGeneralProblem.StrongParity
