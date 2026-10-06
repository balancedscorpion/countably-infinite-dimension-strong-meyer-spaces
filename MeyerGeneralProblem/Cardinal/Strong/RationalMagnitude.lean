module

public import MeyerGeneralProblem.Cardinal.Strong.RationalArctanPerturbation

@[expose] public section

/-! Executable magnitude-sensitive precision, avoiding representation-size blowup. -/

namespace MeyerGeneralProblem.StrongParity

/-- An executable positive integer bound for the VALUE of a rational input. -/
def rationalMagnitude (q : ℚ) : ℕ := q.num.natAbs / q.den + 1

/-- The finite arctangent grid size depends on actual magnitude and precision. -/
def rationalMagnitudeGridSize (q : ℚ) (p : ℕ) : ℕ := rationalMagnitude q * 2 ^ p

/-- Actual rational arctangent computation using the certified magnitude grid. -/
def rationalMagnitudeArctanApprox (q : ℚ) (p : ℕ) : ℚ :=
  rationalArctanQuadrature q (rationalMagnitudeGridSize q p)

noncomputable section

theorem rationalMagnitude_pos (q : ℚ) : 0 < rationalMagnitude q := by
  dsimp [rationalMagnitude]
  exact Nat.zero_lt_succ _

/-- The integer division schedule bounds the actual real value, for BOTH signs. -/
theorem rational_abs_le_magnitude (q : ℚ) : |(q : ℝ)| ≤ (rationalMagnitude q : ℝ) := by
  have hd : 0 < (q.den : ℝ) := Nat.cast_pos.mpr q.den_pos
  have hn : q.num.natAbs ≤ (q.num.natAbs / q.den + 1) * q.den := by
    have he := Nat.mod_add_div q.num.natAbs q.den
    have hm := Nat.mod_lt q.num.natAbs q.den_pos
    nlinarith
  have hnR : (q.num.natAbs : ℝ) ≤ (rationalMagnitude q : ℝ) * (q.den : ℝ) := by
    exact_mod_cast hn
  have ha : |(q.num : ℝ)| = (q.num.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [Rat.cast_def, abs_div, abs_of_pos hd, ha]
  exact (div_le_iff₀ hd).mpr hnR

/-- The executable magnitude grid has certified error at EVERY input and precision. -/
theorem rationalMagnitudeArctanApprox_error (q : ℚ) (p : ℕ) :
    |(rationalMagnitudeArctanApprox q p : ℝ) - Real.arctan (q : ℝ)| ≤ 1 / (2 : ℝ) ^ p := by
  have hN : 0 < rationalMagnitudeGridSize q p := by
    dsimp [rationalMagnitudeGridSize]
    exact Nat.mul_pos (rationalMagnitude_pos q) (by positivity)
  have hm : (rationalMagnitude q : ℝ) ≠ 0 := by exact_mod_cast (rationalMagnitude_pos q).ne'
  rw [rationalMagnitudeArctanApprox, rationalArctanQuadrature_cast]
  calc
    _ ≤ |(q : ℝ)| / rationalMagnitudeGridSize q p := arctanQuadratureLeft_error _ hN
    _ ≤ (rationalMagnitude q : ℝ) / rationalMagnitudeGridSize q p := by
      gcongr
      exact rational_abs_le_magnitude q
    _ = _ := by
      dsimp [rationalMagnitudeGridSize]
      push_cast
      field_simp [hm]

/-- The actual magnitude-based value remains certified under explicit real-input error. -/
theorem rationalMagnitudeArctanApprox_real_error (q : ℚ) (p : ℕ) {x epsilon : ℝ}
    (hq : |(q : ℝ) - x| ≤ epsilon) :
    |(rationalMagnitudeArctanApprox q p : ℝ) - Real.arctan x| ≤ 1 / (2 : ℝ) ^ p + epsilon := by
  calc
    _ ≤ |(rationalMagnitudeArctanApprox q p : ℝ) - Real.arctan (q : ℝ)| +
        |Real.arctan (q : ℝ) - Real.arctan x| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (rationalMagnitudeArctanApprox_error q p)
      ((arctan_abs_sub_le _ _).trans hq)

end

end MeyerGeneralProblem.StrongParity
