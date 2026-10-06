module

public import MeyerGeneralProblem.Cardinal.Strong.PhaseDistance
public import MeyerGeneralProblem.Cardinal.Strong.NativePhysicalGap

@[expose] public section

/-! Exact Gaussian rational arithmetic for the ORIGINAL quarter phases.
Both signs are computed by the complete residue class modulo four. -/

namespace MeyerGeneralProblem.StrongParity

/-- Exact positive quarter-phase multiplication on a rational coefficient. -/
def rationalQuarterCoefficient (n : ℕ) (q : ℚ) : ℚ × ℚ :=
  if n % 4 = 0 then (q, 0) else
  if n % 4 = 1 then (0, q) else
  if n % 4 = 2 then (-q, 0) else (0, -q)

/-- Rational conjugation, computed entirely in the rational coordinates. -/
def rationalComplexConj (q : ℚ × ℚ) : ℚ × ℚ := (q.1, -q.2)

/-- Exact negative quarter-phase multiplication on a rational coefficient. -/
def rationalNegativeQuarterCoefficient (n : ℕ) (q : ℚ) : ℚ × ℚ :=
  rationalComplexConj (rationalQuarterCoefficient n q)

noncomputable section

/-- The actual complex value of a pair of ordinary rational coordinates. -/
def rationalComplexValue (q : ℚ × ℚ) : ℂ := (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

/-- Every original positive quarter phase is an exact power of I. -/
theorem unitPhase_nat_quarter (n : ℕ) : unitPhase ((n : ℝ) / 4) = Complex.I ^ n := by
  unfold unitPhase
  have heq : ((2 * Real.pi * ((n : ℝ) / 4) : ℝ) : ℂ) * Complex.I =
      (n : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) := by push_cast; ring
  rw [heq, Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]

/-- The literal original phase at the negative argument is the conjugate phase. -/
theorem unitPhase_neg_eq_conj (t : ℝ) : unitPhase (-t) = star (unitPhase t) := by
  unfold unitPhase
  change Complex.exp (((2 * Real.pi * -t : ℝ) : ℂ) * Complex.I) =
    (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I))
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Ordinary rational conjugation has the actual original complex value. -/
theorem rationalComplexValue_conj (q : ℚ × ℚ) :
    rationalComplexValue (rationalComplexConj q) = star (rationalComplexValue q) := by
  simp [rationalComplexValue, rationalComplexConj]

/-- The exact rational program equals every original positive quarter-phased coefficient. -/
theorem rationalQuarterCoefficient_value (n : ℕ) (q : ℚ) :
    rationalComplexValue (rationalQuarterCoefficient n q) =
      (q : ℂ) * unitPhase ((n : ℝ) / 4) := by
  rw [unitPhase_nat_quarter, Complex.I_pow_eq_pow_mod]
  have hm : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    have := Nat.mod_lt n (by norm_num : 0 < 4)
    omega
  rcases hm with h | h | h | h <;>
    simp [rationalQuarterCoefficient, rationalComplexValue, h, Complex.I_sq, Complex.I_pow_three]

/-- The exact rational program equals every original negative quarter-phased coefficient. -/
theorem rationalNegativeQuarterCoefficient_value (n : ℕ) (q : ℚ) :
    rationalComplexValue (rationalNegativeQuarterCoefficient n q) =
      (q : ℂ) * unitPhase (-(n : ℝ) / 4) := by
  rw [rationalNegativeQuarterCoefficient, rationalComplexValue_conj,
    rationalQuarterCoefficient_value]
  rw [show -(n : ℝ) / 4 = -((n : ℝ) / 4) by ring, unitPhase_neg_eq_conj]
  simp

end

end MeyerGeneralProblem.StrongParity
