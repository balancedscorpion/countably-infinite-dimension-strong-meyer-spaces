module

public import MeyerGeneralProblem.Cardinal.Strong.RationalNamedRootSearch

@[expose] public section

/-! Actual rational certified intervals for EVERY original labelled root. -/

namespace MeyerGeneralProblem.StrongParity

/-- The executable certified lower endpoint for the actual original root. -/
def rationalOriginalRootLower (a : ℚ) (n : ℤ) (p : ℕ) : ℚ :=
  rationalOriginalRootApprox a n p - rationalBinaryRadius p

/-- The executable certified upper endpoint for the actual original root. -/
def rationalOriginalRootUpper (a : ℚ) (n : ℤ) (p : ℕ) : ℚ :=
  rationalOriginalRootApprox a n p + rationalBinaryRadius p

/-- The executable lower endpoint consuming the actual real parameter name. -/
def rationalNamedOriginalRootLower (name : ℕ → ℚ) (n : ℤ) (p : ℕ) : ℚ :=
  rationalNamedOriginalRootApprox name n p - rationalBinaryRadius p

/-- The executable upper endpoint consuming the actual real parameter name. -/
def rationalNamedOriginalRootUpper (name : ℕ → ℚ) (n : ℤ) (p : ℕ) : ℚ :=
  rationalNamedOriginalRootApprox name n p + rationalBinaryRadius p

noncomputable section

/-- The emitted rational interval contains the ACTUAL original labelled root. -/
theorem rationalOriginalRoot_interval {a : ℚ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (n : ℤ) (p : ℕ) :
    (rationalOriginalRootLower a n p : ℝ) ≤
      sheetRootLabel (a : ℝ) (by exact_mod_cast ha) (rationalCompactParameter_lt_one ha2) n ∧
    sheetRootLabel (a : ℝ) (by exact_mod_cast ha) (rationalCompactParameter_lt_one ha2) n ≤
      (rationalOriginalRootUpper a n p : ℝ) := by
  have h := abs_le.mp (rationalOriginalRootApprox_error ha ha2 n p)
  simp only [rationalOriginalRootLower, rationalOriginalRootUpper, Rat.cast_sub, Rat.cast_add,
    rationalBinaryRadius_cast]
  constructor <;> linarith [h.1, h.2]

/-- The emitted interval contains the root of the ACTUAL named real parameter. -/
theorem rationalNamedOriginalRoot_interval (name : ℕ → ℚ) {a : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hname_range : ∀ m, 0 ≤ name m ∧ name m ≤ 1 / 2)
    (hname_error : ∀ m, |(name m : ℝ) - a| ≤ 1 / (2 : ℝ) ^ m)
    (n : ℤ) (p : ℕ) :
    (rationalNamedOriginalRootLower name n p : ℝ) ≤
      sheetRootLabel a ha (by linarith : a < 1) n ∧
    sheetRootLabel a ha (by linarith : a < 1) n ≤
      (rationalNamedOriginalRootUpper name n p : ℝ) := by
  have h := abs_le.mp (rationalNamedOriginalRootApprox_error name ha ha2 hname_range hname_error n p)
  simp only [rationalNamedOriginalRootLower, rationalNamedOriginalRootUpper, Rat.cast_sub,
    Rat.cast_add, rationalBinaryRadius_cast]
  constructor <;> linarith [h.1, h.2]

/-- The exact computable width of every emitted original root interval. -/
theorem rationalOriginalRoot_interval_width (a : ℚ) (n : ℤ) (p : ℕ) :
    rationalOriginalRootUpper a n p - rationalOriginalRootLower a n p = 2 * rationalBinaryRadius p := by
  dsimp [rationalOriginalRootUpper, rationalOriginalRootLower]
  ring

/-- The exact computable width of every emitted real-parameter root interval. -/
theorem rationalNamedOriginalRoot_interval_width (name : ℕ → ℚ) (n : ℤ) (p : ℕ) :
    rationalNamedOriginalRootUpper name n p - rationalNamedOriginalRootLower name n p =
      2 * rationalBinaryRadius p := by
  dsimp [rationalNamedOriginalRootUpper, rationalNamedOriginalRootLower]
  ring

end

end MeyerGeneralProblem.StrongParity
