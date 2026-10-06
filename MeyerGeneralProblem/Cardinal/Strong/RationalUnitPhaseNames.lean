module

public import MeyerGeneralProblem.Cardinal.Strong.RationalTrigPerturbation
public import MeyerGeneralProblem.Cardinal.Strong.RationalComplexArithmetic
public import MeyerGeneralProblem.Cardinal.Strong.FiniteOriginalCoefficientBounds
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-! Ordinary unit-phase names with a size bound computed from the input name
itself. No supplied real-size or phase-accuracy certificate is used by the program. -/

namespace MeyerGeneralProblem.StrongParity

/-- Integer size budget read from the zero-precision rational input. -/
def rationalRealNameSize (name : ℕ → ℚ) : ℕ := ⌈|name 0|⌉₊ + 1

/-- Whole complex phase error budget, including input and pi errors. -/
def rationalUnitPhaseSensitivity (name : ℕ → ℚ) : ℕ :=
  2 * (1 + 2 * (5 + rationalRealNameSize name))

/-- Finite rational sine/cosine composition at a specified entry precision. -/
def rationalNamedUnitPhaseAt (name : ℕ → ℚ) (p : ℕ) : ℚ × ℚ :=
  let angle := 2 * rationalPiApprox p * name p
  (rationalBoundedCosApprox angle p, rationalBoundedSinApprox angle p)

/-- Ordinary binary name of the complete complex unit phase, with internal budgeting. -/
def rationalNamedUnitPhase (name : ℕ → ℚ) (p : ℕ) : ℚ × ℚ :=
  rationalNamedUnitPhaseAt name (p + rationalUnitPhaseSensitivity name)

noncomputable section

/-- A valid binary real name supplies its actual size bound internally. -/
theorem rationalRealNameSize_bound (name : ℕ → ℚ) {x : ℝ}
    (hname : ∀ p, |(name p : ℝ) - x| ≤ 1 / (2 : ℝ) ^ p) :
    |x| ≤ (rationalRealNameSize name : ℝ) := by
  have h0 := hname 0
  have hq : (|name 0| : ℚ) ≤ (⌈|name 0|⌉₊ : ℚ) := Nat.le_ceil _
  have hc : |(name 0 : ℝ)| ≤ (⌈|name 0|⌉₊ : ℝ) := by exact_mod_cast hq
  have h := abs_add_le (x - (name 0 : ℝ)) (name 0 : ℝ)
  rw [sub_add_cancel, abs_sub_comm] at h
  simp only [pow_zero, div_one] at h0
  simp only [rationalRealNameSize, Nat.cast_add, Nat.cast_one]
  linarith

/-- Every pi approximant has the fixed safe bound used by the phase program. -/
theorem rationalPiApprox_abs_le_five (p : ℕ) : |(rationalPiApprox p : ℝ)| ≤ 5 := by
  have he := rationalPiApprox_error p
  have hb : 1 / (2 : ℝ) ^ p ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ p)
  have h := abs_add_le ((rationalPiApprox p : ℝ) - Real.pi) Real.pi
  rw [sub_add_cancel, abs_of_pos Real.pi_pos] at h
  linarith [Real.pi_lt_four]

/-- The actual angle error includes BOTH the computed input and pi approximations. -/
theorem rationalNamedUnitPhase_angle_error (name : ℕ → ℚ) {x : ℝ}
    (hname : ∀ p, |(name p : ℝ) - x| ≤ 1 / (2 : ℝ) ^ p) (p : ℕ) :
    |((2 * rationalPiApprox p * name p : ℚ) : ℝ) - 2 * Real.pi * x| ≤
      ((2 * (5 + rationalRealNameSize name) : ℕ) : ℝ) * (1 / (2 : ℝ) ^ p) := by
  have heq : ((2 * rationalPiApprox p * name p : ℚ) : ℝ) - 2 * Real.pi * x =
      2 * ((rationalPiApprox p : ℝ) * ((name p : ℝ) - x) +
        ((rationalPiApprox p : ℝ) - Real.pi) * x) := by push_cast; ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsum : |(rationalPiApprox p : ℝ) * ((name p : ℝ) - x) +
      ((rationalPiApprox p : ℝ) - Real.pi) * x| ≤
      5 * (1 / (2 : ℝ) ^ p) + (1 / (2 : ℝ) ^ p) * (rationalRealNameSize name : ℝ) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul (rationalPiApprox_abs_le_five p) (hname p) (abs_nonneg _) (by norm_num))
      (mul_le_mul (rationalPiApprox_error p) (rationalRealNameSize_bound name hname)
        (abs_nonneg _) (by positivity))
  calc
    _ ≤ 2 * (5 * (1 / (2 : ℝ) ^ p) +
      (1 / (2 : ℝ) ^ p) * (rationalRealNameSize name : ℝ)) := by linarith
    _ = _ := by push_cast; ring

/-- Every output complex phase is uniformly bounded without a real oracle. -/
theorem rationalNamedUnitPhaseAt_norm_le_two (name : ℕ → ℚ) (p : ℕ) :
    ‖rationalComplexValue (rationalNamedUnitPhaseAt name p)‖ ≤ 2 := by
  let angle := 2 * rationalPiApprox p * name p
  have hc := rationalUnitClamp_bounds (rationalCosApprox angle p)
  have hs := rationalUnitClamp_bounds (rationalSinApprox angle p)
  have hc' : |(rationalBoundedCosApprox angle p : ℝ)| ≤ 1 := by
    exact_mod_cast (abs_le.mpr hc)
  have hs' : |(rationalBoundedSinApprox angle p : ℝ)| ≤ 1 := by
    exact_mod_cast (abs_le.mpr hs)
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  convert! add_le_add hc' hs' using 1 <;>
    norm_num [rationalNamedUnitPhaseAt, rationalComplexValue, angle]

/-- The complete complex output obeys its computed input/pi/trigonometric budget. -/
theorem rationalNamedUnitPhaseAt_error (name : ℕ → ℚ) {x : ℝ}
    (hname : ∀ p, |(name p : ℝ) - x| ≤ 1 / (2 : ℝ) ^ p) (p : ℕ) :
    ‖rationalComplexValue (rationalNamedUnitPhaseAt name p) - unitPhase x‖ ≤
      (rationalUnitPhaseSensitivity name : ℝ) * (1 / (2 : ℝ) ^ p) := by
  let angle := 2 * rationalPiApprox p * name p
  have he := rationalNamedUnitPhase_angle_error name hname p
  have hc := rationalBoundedCosApprox_real_input_error angle p he
  have hs := rationalBoundedSinApprox_real_input_error angle p he
  have hw : unitPhase x = (Real.cos (2 * Real.pi * x) : ℂ) +
      (Real.sin (2 * Real.pi * x) : ℂ) * Complex.I := Complex.exp_ofReal_mul_I _
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  rw [hw]
  simp only [rationalNamedUnitPhaseAt, rationalComplexValue, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im,
    mul_one, zero_add]
  convert! add_le_add hc hs using 1 <;>
    simp [rationalUnitPhaseSensitivity, angle] <;> push_cast <;> ring

/-- Internally budgeted unit-phase names have the requested complex binary error. -/
theorem rationalNamedUnitPhase_error (name : ℕ → ℚ) {x : ℝ}
    (hname : ∀ p, |(name p : ℝ) - x| ≤ 1 / (2 : ℝ) ^ p) (p : ℕ) :
    ‖rationalComplexValue (rationalNamedUnitPhase name p) - unitPhase x‖ ≤ 1 / (2 : ℝ) ^ p :=
  (rationalNamedUnitPhaseAt_error name hname (p + rationalUnitPhaseSensitivity name)).trans
    (integer_sensitivity_binary_shift (rationalUnitPhaseSensitivity name) p)

/-- Every internally budgeted complex phase output still has the same uniform bound. -/
theorem rationalNamedUnitPhase_norm_le_two (name : ℕ → ℚ) (p : ℕ) :
    ‖rationalComplexValue (rationalNamedUnitPhase name p)‖ ≤ 2 :=
  rationalNamedUnitPhaseAt_norm_le_two name _

end

end MeyerGeneralProblem.StrongParity
