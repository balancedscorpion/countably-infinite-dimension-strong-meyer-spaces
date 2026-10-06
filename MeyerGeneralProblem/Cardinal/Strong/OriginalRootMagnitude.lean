module

public import MeyerGeneralProblem.Cardinal.Strong.SheetRootLabels

@[expose] public section

/-! A complete integer search radius for EVERY actual original native root. -/

namespace MeyerGeneralProblem.StrongParity

/-- The executable integer radius enclosing the entire labelled root bracket. -/
def originalRootSearchRadius (n : ℤ) : ℕ := n.natAbs + 1

noncomputable section

/-- Every actual original root is inside the definite integer search radius. -/
theorem sheetRootLabel_search_radius (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℤ) :
    -(originalRootSearchRadius n : ℝ) ≤ sheetRootLabel a ha ha1 n ∧
      sheetRootLabel a ha ha1 n ≤ originalRootSearchRadius n := by
  have hb : 0 < 1 + beta := by linarith [beta_between_three_four]
  have hb4 : 4 < 1 + beta := by linarith [beta_between_three_four]
  have hn : |(n : ℝ)| = (n.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hnlo : -(n.natAbs : ℝ) ≤ (n : ℝ) := by simpa only [← hn] using neg_abs_le (n : ℝ)
  have hnhi : (n : ℝ) ≤ (n.natAbs : ℝ) := by simpa only [← hn] using le_abs_self (n : ℝ)
  have hnp : (0 : ℝ) ≤ n.natAbs := Nat.cast_nonneg _
  have hbr := sheetRootLabel_in_bracket a ha ha1 n
  have hl : -(n.natAbs : ℝ) - 1 ≤ sheetRootBracketLower n := by
    dsimp [sheetRootBracketLower]
    apply (le_div_iff₀ hb).mpr
    have hm := mul_nonneg hnp (by linarith : 0 ≤ beta)
    nlinarith
  have hu : sheetRootBracketUpper n ≤ (n.natAbs : ℝ) + 1 := by
    dsimp [sheetRootBracketUpper]
    apply (div_le_iff₀ hb).mpr
    have hm := mul_nonneg hnp (by linarith : 0 ≤ beta)
    nlinarith
  simp only [originalRootSearchRadius, Nat.cast_add, Nat.cast_one]
  exact ⟨by linarith [hbr.1], by linarith [hbr.2]⟩

end

end MeyerGeneralProblem.StrongParity
