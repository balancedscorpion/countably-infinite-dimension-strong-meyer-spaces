module

public import MeyerGeneralProblem.Cardinal.Strong.RationalTrigTaylor
public import MeyerGeneralProblem.Cardinal.Strong.RationalMagnitude

@[expose] public section

/-! Definite finite rational sine/cosine programs with uniform binary errors. -/

namespace MeyerGeneralProblem.StrongParity

/-- Half the definite Taylor term count, using actual rational magnitude and precision. -/
def rationalTrigHalfDegree (q : ℚ) (p : ℕ) : ℕ :=
  2 * rationalMagnitude q ^ 2 + p

/-- The executable positive Taylor term count. -/
def rationalTrigTermCount (q : ℚ) (p : ℕ) : ℕ := 2 * rationalTrigHalfDegree q p

/-- An executable finite rational sine approximation at binary precision `p`. -/
def rationalSinApprox (q : ℚ) (p : ℕ) : ℚ := rationalSinTaylor q (rationalTrigTermCount q p)

/-- An executable finite rational cosine approximation at binary precision `p`. -/
def rationalCosApprox (q : ℚ) (p : ℕ) : ℚ := rationalCosTaylor q (rationalTrigTermCount q p)

noncomputable section

theorem rationalTrigTermCount_pos (q : ℚ) (p : ℕ) : 0 < rationalTrigTermCount q p := by
  dsimp [rationalTrigTermCount, rationalTrigHalfDegree]
  have h := rationalMagnitude_pos q
  positivity

/-- The definite degree pays the ENTIRE factorial remainder without a search oracle. -/
theorem rationalTrig_factorial_bound (M p : ℕ) :
    M ^ (2 * (2 * M ^ 2 + p)) * 2 ^ p ≤ (2 * (2 * M ^ 2 + p)).factorial := by
  let k := 2 * M ^ 2 + p
  have hp : p ≤ k := by dsimp [k]; omega
  have hb : 2 * M ^ 2 ≤ k + 1 := by dsimp [k]; omega
  have hf : 1 ≤ k.factorial := Nat.factorial_pos k
  calc
    M ^ (2 * k) * 2 ^ p ≤ M ^ (2 * k) * 2 ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < 2) hp)
    _ = (2 * M ^ 2) ^ k := by rw [pow_mul, mul_pow]; ac_rfl
    _ ≤ (k + 1) ^ k := Nat.pow_le_pow_left hb k
    _ ≤ k.factorial * (k + 1) ^ k := by simpa using Nat.mul_le_mul_right ((k + 1) ^ k) hf
    _ ≤ (k + k).factorial := Nat.factorial_mul_pow_le_factorial
    _ = (2 * k).factorial := by rw [Nat.two_mul]

/-- Uniform remainder bound at the actual finite term count. -/
theorem rationalTrig_precision_remainder (q : ℚ) (p : ℕ) :
    |(q : ℝ)| ^ rationalTrigTermCount q p / (rationalTrigTermCount q p).factorial ≤
      1 / (2 : ℝ) ^ p := by
  have hf : 0 < ((rationalTrigTermCount q p).factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hb := rationalTrig_factorial_bound (rationalMagnitude q) p
  have hbR : (rationalMagnitude q : ℝ) ^ rationalTrigTermCount q p * (2 : ℝ) ^ p ≤
      ((rationalTrigTermCount q p).factorial : ℝ) := by
    exact_mod_cast hb
  have hm := pow_le_pow_left₀ (abs_nonneg (q : ℝ)) (rational_abs_le_magnitude q)
    (rationalTrigTermCount q p)
  apply (div_le_div_iff₀ hf (by positivity : 0 < (2 : ℝ) ^ p)).mpr
  simpa using (mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ (2 : ℝ) ^ p)).trans hbR

/-- Actual sine error, valid for EVERY signed rational input and precision. -/
theorem rationalSinApprox_error (q : ℚ) (p : ℕ) :
    |(rationalSinApprox q p : ℝ) - Real.sin (q : ℝ)| ≤ 1 / (2 : ℝ) ^ p := by
  have h := rationalSinTaylor_error q (rationalTrigTermCount q p - 1)
  rw [Nat.sub_add_cancel (rationalTrigTermCount_pos q p)] at h
  exact h.trans (rationalTrig_precision_remainder q p)

/-- Actual cosine error, valid for EVERY signed rational input and precision. -/
theorem rationalCosApprox_error (q : ℚ) (p : ℕ) :
    |(rationalCosApprox q p : ℝ) - Real.cos (q : ℝ)| ≤ 1 / (2 : ℝ) ^ p := by
  have h := rationalCosTaylor_error q (rationalTrigTermCount q p - 1)
  rw [Nat.sub_add_cancel (rationalTrigTermCount_pos q p)] at h
  exact h.trans (rationalTrig_precision_remainder q p)

end

end MeyerGeneralProblem.StrongParity
