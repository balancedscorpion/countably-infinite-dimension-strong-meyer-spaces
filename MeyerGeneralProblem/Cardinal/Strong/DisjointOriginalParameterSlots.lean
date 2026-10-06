module

public import MeyerGeneralProblem.Cardinal.Strong.CoupledOriginalRootExclusions

@[expose] public section

/-! Explicit ordinary disjoint slots strictly inside the accepted original compact domain. -/

namespace MeyerGeneralProblem.StrongParity

/-- The definite rational dyadic length used for the assigned original sheet slot. -/
def originalParameterSlotLength (i : ℕ) : ℚ := 1 / (2 : ℚ) ^ (i + 3)

/-- Every actual assigned slot length is positive. -/
theorem originalParameterSlotLength_pos (i : ℕ) : 0 < originalParameterSlotLength i := by
  unfold originalParameterSlotLength
  positivity

/-- Every assigned slot length is at most one eighth. -/
theorem originalParameterSlotLength_le_eighth (i : ℕ) : originalParameterSlotLength i ≤ 1 / 8 := by
  have h : (8 : ℚ) ≤ 2 ^ (i + 3) := by
    calc
      8 = (2 : ℚ) ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  exact one_div_le_one_div_of_le (by norm_num) h

/-- Every later assigned slot length is at most half of an earlier one. -/
theorem originalParameterSlotLength_later {i j : ℕ} (hji : j < i) :
    originalParameterSlotLength i ≤ originalParameterSlotLength j / 2 := by
  calc
    _ ≤ 1 / (2 : ℚ) ^ (j + 4) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    _ = _ := by
      unfold originalParameterSlotLength
      rw [show j + 4 = (j + 3) + 1 by omega, pow_succ]
      field_simp

/-- The actual disjoint assigned original slots, with every bound supplied internally. -/
def disjointOriginalParameterSlot (i : ℕ) : RationalParameterSlot where
  lower := 1 / 4 + originalParameterSlotLength i
  upper := 1 / 4 + (3 / 2) * originalParameterSlotLength i
  lower_pos := by have h := originalParameterSlotLength_pos i; linarith
  upper_le_half := by have h := originalParameterSlotLength_le_eighth i; linarith
  lower_lt_upper := by have h := originalParameterSlotLength_pos i; linarith

/-- Every assigned original slot lies strictly above one quarter and below one half. -/
theorem disjointOriginalParameterSlot_bounds (i : ℕ) :
    1 / 4 < (disjointOriginalParameterSlot i).lower ∧
      (disjointOriginalParameterSlot i).upper < 1 / 2 := by
  have h := originalParameterSlotLength_pos i
  have hh := originalParameterSlotLength_le_eighth i
  constructor <;> dsimp [disjointOriginalParameterSlot] <;> linarith

/-- Every later closed slot lies strictly below every earlier closed slot. -/
theorem disjointOriginalParameterSlot_separated {i j : ℕ} (hji : j < i) :
    (disjointOriginalParameterSlot i).upper < (disjointOriginalParameterSlot j).lower := by
  have h := originalParameterSlotLength_later hji
  have hp := originalParameterSlotLength_pos j
  dsimp [disjointOriginalParameterSlot]
  linarith

noncomputable section

/-- Every actual coupled value in these explicit slots is inside the accepted open compact range. -/
theorem coupledOriginalParameterValue_disjoint_range (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (i : ℕ) : coupledOriginalParameterValue scales hpos disjointOriginalParameterSlot i ∈
      Set.Ioo (1 / 4 : ℝ) (1 / 2) := by
  have h := coupledOriginalParameterValue_interior scales hpos disjointOriginalParameterSlot i
  have hh := disjointOriginalParameterSlot_bounds i
  have hl : (1 / 4 : ℝ) < ((disjointOriginalParameterSlot i).lower : ℝ) := by
    have hc : ((1 / 4 : ℚ) : ℝ) < ((disjointOriginalParameterSlot i).lower : ℝ) := by
      exact_mod_cast hh.1
    norm_num at hc
    exact hc
  have hu : ((disjointOriginalParameterSlot i).upper : ℝ) < 1 / 2 := by
    have hc : ((disjointOriginalParameterSlot i).upper : ℝ) < ((1 / 2 : ℚ) : ℝ) := by
      exact_mod_cast hh.2
    norm_num at hc
    exact hc
  exact ⟨hl.trans h.1, h.2.trans hu⟩

/-- Actual coupled parameters are strictly antitone in the explicit disjoint assigned slots. -/
theorem coupledOriginalParameterValue_disjoint_strictAnti (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) :
    StrictAnti (coupledOriginalParameterValue scales hpos disjointOriginalParameterSlot) := by
  intro j i hji
  have hj := (coupledOriginalParameterValue_interior scales hpos disjointOriginalParameterSlot j).1
  have hi := (coupledOriginalParameterValue_interior scales hpos disjointOriginalParameterSlot i).2
  have hsep : ((disjointOriginalParameterSlot i).upper : ℝ) <
      ((disjointOriginalParameterSlot j).lower : ℝ) := by
    exact_mod_cast disjointOriginalParameterSlot_separated hji
  exact hi.trans (hsep.trans hj)

/-- The actual constructed parameters are distinct across all sheets, with no disjointness input. -/
theorem coupledOriginalParameterValue_disjoint_injective (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) :
    Function.Injective (coupledOriginalParameterValue scales hpos disjointOriginalParameterSlot) :=
  (coupledOriginalParameterValue_disjoint_strictAnti scales hpos).injective

end

end MeyerGeneralProblem.StrongParity
