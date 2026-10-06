module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalRootSearch

@[expose] public section

/-! Actual original root computation from a binary rational parameter name.
The finite program consumes the name at one definite precision. The final
collision-free compact names must still be constructed; none is postulated
in a final strong-carrier existence theorem.
-/

namespace MeyerGeneralProblem.StrongParity

/-- The actual finite original root program from a supplied rational parameter name. -/
def rationalNamedOriginalRootApprox (name : ℕ → ℚ) (n : ℤ) (p : ℕ) : ℚ :=
  rationalOriginalRootSearchWith
    (fun x => rationalSheetRootPhaseApprox (name (p + 6)) x (p + 5)) n p

noncomputable section

/-- The finite program computes EVERY actual labelled root of a valid compact parameter name. -/
theorem rationalNamedOriginalRootApprox_error (name : ℕ → ℚ) {a : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hname_range : ∀ m, 0 ≤ name m ∧ name m ≤ 1 / 2)
    (hname_error : ∀ m, |(name m : ℝ) - a| ≤ 1 / (2 : ℝ) ^ m)
    (n : ℤ) (p : ℕ) :
    |(rationalNamedOriginalRootApprox name n p : ℝ) -
      sheetRootLabel a ha (by linarith : a < 1) n| ≤ 1 / (2 : ℝ) ^ p := by
  apply rationalOriginalRootSearchWith_error _ ha ha2 n p
  intro q
  apply (rationalSheetRootPhaseApprox_real_parameter_error
    (hname_range (p + 6)).1 (hname_range (p + 6)).2 ha ha2 (hname_error (p + 6)) q (p + 5)).trans_eq
  simp only [pow_add]
  norm_num
  field_simp
  norm_num

end

end MeyerGeneralProblem.StrongParity
