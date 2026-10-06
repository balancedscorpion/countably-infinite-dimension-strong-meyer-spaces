module

public import MeyerGeneralProblem.Cardinal.Strong.RationalScaledOriginalRoot

@[expose] public section

/-! Ordinary coarse-module values with safe reciprocal and explicit binary errors. -/

namespace MeyerGeneralProblem.StrongParity

/-- The exact rational raw coarse value using the implemented beta and dilation programs. -/
def rationalCoarseRaw (u v : ℚ) (p : ℕ) : ℚ :=
  (u + rationalBetaApprox p * v) / rationalDilationApprox p

/-- An executable integer bound paying both signed rational coarse coefficients. -/
def coarseValueErrorCoefficient (u v : ℚ) : ℕ := rationalMagnitude u + 5 * rationalMagnitude v

/-- The ordinary coarse-module computation at the requested binary precision. -/
def rationalCoarseApprox (u v : ℚ) (p : ℕ) : ℚ :=
  rationalCoarseRaw u v (p + coarseValueErrorCoefficient u v)

noncomputable section

/-- Inversion on [1,infinity) does not amplify input error. -/
theorem inv_abs_sub_le_of_one_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |x⁻¹ - y⁻¹| ≤ |x - y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hxy : 1 ≤ x * y := by nlinarith
  have he : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by field_simp
  rw [he, abs_div, abs_mul, abs_of_pos hx0, abs_of_pos hy0, abs_sub_comm]
  exact (div_le_self (abs_nonneg _) hxy)

/-- The computed reciprocal dilation is safely bounded by one. -/
theorem rationalDilationApprox_inv_abs_le_one (p : ℕ) :
    |(rationalDilationApprox p : ℝ)⁻¹| ≤ 1 := by
  have h : (1 : ℝ) ≤ (rationalDilationApprox p : ℝ) := by
    exact_mod_cast (rationalDilationApprox_range p).1
  rw [abs_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ h

/-- The actual raw coarse error pays the two rational magnitudes with an integer bound. -/
theorem rationalCoarseRaw_error (u v : ℚ) (p : ℕ) :
    |(rationalCoarseRaw u v p : ℝ) - rationalCoarseValue u v| ≤
      (coarseValueErrorCoefficient u v : ℝ) * (1 / (2 : ℝ) ^ p) := by
  let c := (rationalDilationApprox p : ℝ)
  let bh := (rationalBetaApprox p : ℝ)
  have hc : 1 ≤ c := by
    dsimp [c]
    exact_mod_cast (rationalDilationApprox_range p).1
  have hic : |c⁻¹| ≤ 1 := rationalDilationApprox_inv_abs_le_one p
  have hie : |c⁻¹ - parityDilationUnit⁻¹| ≤ 1 / (2 : ℝ) ^ p :=
    (inv_abs_sub_le_of_one_le hc parityDilationUnit_one_le).trans (rationalDilationApprox_error p)
  have hb : |bh - beta| ≤ 1 / (2 : ℝ) ^ p := rationalBetaApprox_error p
  have hbeta : |beta| ≤ 4 := by
    rw [abs_of_nonneg (by linarith [beta_between_three_four] : 0 ≤ beta)]
    exact beta_between_three_four.2.le
  have hnum : |(u : ℝ) + beta * (v : ℝ)| ≤ |(u : ℝ)| + 4 * |(v : ℝ)| := by
    calc
      _ ≤ |(u : ℝ)| + |beta * (v : ℝ)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul]; gcongr
  have he : (rationalCoarseRaw u v p : ℝ) - rationalCoarseValue u v =
      (bh - beta) * (v : ℝ) * c⁻¹ +
      ((u : ℝ) + beta * (v : ℝ)) * (c⁻¹ - parityDilationUnit⁻¹) := by
    simp only [rationalCoarseRaw, Rat.cast_div, Rat.cast_add, Rat.cast_mul, rationalCoarseValue]
    dsimp [bh, c]
    ring
  rw [he]
  calc
    _ ≤ |(bh - beta) * (v : ℝ) * c⁻¹| +
        |((u : ℝ) + beta * (v : ℝ)) * (c⁻¹ - parityDilationUnit⁻¹)| := abs_add_le _ _
    _ = |bh - beta| * |(v : ℝ)| * |c⁻¹| +
        |(u : ℝ) + beta * (v : ℝ)| * |c⁻¹ - parityDilationUnit⁻¹| := by simp only [abs_mul]
    _ ≤ (1 / (2 : ℝ) ^ p) * |(v : ℝ)| * 1 +
        (|(u : ℝ)| + 4 * |(v : ℝ)|) * (1 / (2 : ℝ) ^ p) := by gcongr
    _ = (|(u : ℝ)| + 5 * |(v : ℝ)|) * (1 / (2 : ℝ) ^ p) := by ring
    _ ≤ ((rationalMagnitude u : ℝ) + 5 * (rationalMagnitude v : ℝ)) *
        (1 / (2 : ℝ) ^ p) := by gcongr; exact rational_abs_le_magnitude u; exact rational_abs_le_magnitude v
    _ = _ := by simp only [coarseValueErrorCoefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

/-- Every actual encoded coarse-module value is computed with the requested binary error. -/
theorem rationalCoarseApprox_error (u v : ℚ) (p : ℕ) :
    |(rationalCoarseApprox u v p : ℝ) - rationalCoarseValue u v| ≤ 1 / (2 : ℝ) ^ p :=
  (rationalCoarseRaw_error u v _).trans
    (nat_coefficient_binary_error (coarseValueErrorCoefficient u v) p)

end

end MeyerGeneralProblem.StrongParity
