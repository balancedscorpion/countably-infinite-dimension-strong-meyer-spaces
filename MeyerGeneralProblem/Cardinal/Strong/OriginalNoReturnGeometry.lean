module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalLiouvilleMask
public import MeyerGeneralProblem.Cardinal.Strong.OriginalQuadraticSpacing

@[expose] public section

/-!
# Genuine physical no-return along the literal Liouville denominators

The complete translated quadrants have no points in the quartically shrinking
return window. The proof combines their global ORIGINAL coordinate bound with
the integer norm of the literal private quadratic scale. Every constant and
eventual return exclusion is supplied internally.
-/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open Filter

/-- Coordinate bound on EVERY actual point, at its exact original module label. -/
theorem translatedCone_second_coordinate_scaled_le (A B : ℤ) (scale : ℝ)
    (hs : 0 < scale) (z : Bool × (ℕ × ℕ)) :
    |((translatedConeCoordinates A B z).2 : ℝ)| ≤
      originalMaskConeConstant A B scale * (1 + |translatedConeFrequency A B z / scale|) := by
  have h := translatedConeCoordinates_second_abs_le A B z
  have he : |translatedConeFrequency A B z| =
      scale * |translatedConeFrequency A B z / scale| := by
    rw [abs_div, abs_of_pos hs]
    field_simp
  rw [he] at h
  unfold originalMaskConeConstant
  have hx := abs_nonneg (translatedConeFrequency A B z / scale)
  have hv := abs_nonneg (translatedConeVertex A B)
  have hb := abs_nonneg (B : ℝ)
  nlinarith

/-- The internally computed return-window coordinate constant at a fixed original label. -/
def originalNoReturnCoordinateConstant (A B : ℤ) (scale : ℝ)
    (z : Bool × (ℕ × ℕ)) : ℝ :=
  originalMaskConeConstant A B scale *
    (2 + |translatedConeFrequency A B z / scale| + scale) +
      |((translatedConeCoordinates A B z).2 : ℝ)|

theorem originalNoReturnCoordinateConstant_nonneg (A B : ℤ) (scale : ℝ)
    (hs : 0 < scale) (z : Bool × (ℕ × ℕ)) :
    0 ≤ originalNoReturnCoordinateConstant A B scale z := by
  have hC := originalMaskConeConstant_pos A B scale hs
  unfold originalNoReturnCoordinateConstant
  positivity

/-- Near the putative return, ALL second-coordinate differences are at most a fixed D*b. -/
theorem originalNoReturn_near_coordinate_le (A B : ℤ) (scale : ℝ) (hs : 0 < scale)
    (z w : Bool × (ℕ × ℕ)) (b : ℝ) (hb : 1 ≤ b)
    (hnear : |translatedConeFrequency A B w / scale -
      (translatedConeFrequency A B z / scale - scale * b)| ≤ 1 / b ^ 4) :
    |((translatedConeCoordinates A B w).2 : ℝ) -
        ((translatedConeCoordinates A B z).2 : ℝ)| ≤
      originalNoReturnCoordinateConstant A B scale z * b := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hrad : 1 / b ^ 4 ≤ (1 : ℝ) := (div_le_one (pow_pos hbpos 4)).mpr (one_le_pow₀ hb)
  have hy : |translatedConeFrequency A B w / scale| ≤
      1 + |translatedConeFrequency A B z / scale| + scale * b := by
    have h := abs_add_le
      (translatedConeFrequency A B w / scale - (translatedConeFrequency A B z / scale - scale * b))
      (translatedConeFrequency A B z / scale - scale * b)
    rw [sub_add_cancel] at h
    have ht := abs_sub (translatedConeFrequency A B z / scale) (scale * b)
    rw [abs_of_pos (mul_pos hs hbpos)] at ht
    linarith
  have hw := translatedCone_second_coordinate_scaled_le A B scale hs w
  have hdiff := abs_sub ((translatedConeCoordinates A B w).2 : ℝ)
    ((translatedConeCoordinates A B z).2 : ℝ)
  have hC := originalMaskConeConstant_pos A B scale hs
  have hstep : |((translatedConeCoordinates A B w).2 : ℝ)| ≤
      originalMaskConeConstant A B scale *
        (2 + |translatedConeFrequency A B z / scale| + scale * b) := by
    calc
      _ ≤ originalMaskConeConstant A B scale * (1 + |translatedConeFrequency A B w / scale|) := hw
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hC.le
  have hbase : 0 ≤ 2 + |translatedConeFrequency A B z / scale| := by positivity
  have htarget : 0 ≤ |((translatedConeCoordinates A B z).2 : ℝ)| := abs_nonneg _
  unfold originalNoReturnCoordinateConstant
  nlinarith [mul_nonneg hC.le hbase,
    mul_le_mul_of_nonneg_left hb htarget,
    mul_le_mul_of_nonneg_left hb (mul_nonneg hC.le hbase)]

/-- A putative return would violate the exact quantitative quadratic spacing bound. -/
theorem originalNoReturn_near_obstruction (A B : ℤ) (m : ℕ) (hm : 0 < m)
    (z w : Bool × (ℕ × ℕ)) (n : ℕ)
    (hnear : |translatedConeFrequency A B w / originalPrivateScale m -
      (translatedConeFrequency A B z / originalPrivateScale m -
        originalPrivateScale m * (denominator (n + 1) : ℝ))| ≤
          1 / (denominator (n + 1) : ℝ) ^ 4) :
    1 ≤ (2 * originalQuadraticScale m + 1) *
      (originalPrivateScale m / (denominator (n + 1) : ℝ) +
        originalNoReturnCoordinateConstant A B (originalPrivateScale m) z *
          ((denominator (n + 1) : ℝ) ^ 3 * |originalMaskError n|)) := by
  let b : ℝ := denominator (n + 1)
  let a : ℝ := numerator (n + 1)
  let t : ℝ := translatedConeFrequency A B z / originalPrivateScale m
  let y : ℝ := translatedConeFrequency A B w / originalPrivateScale m
  let q : ℤ := (translatedConeCoordinates A B w).2 - (translatedConeCoordinates A B z).2
  let p : ℤ := (translatedConeCoordinates A B w).1 - (translatedConeCoordinates A B z).1
  let k : ℤ := -(denominator (n + 1) * p + numerator (n + 1) * q)
  have hs := originalPrivateScale_pos m hm
  have hb : 1 ≤ b := by dsimp [b]; exact_mod_cast denominator_pos (n + 1)
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hq : |(q : ℝ)| ≤ originalNoReturnCoordinateConstant A B (originalPrivateScale m) z * b := by
    simpa only [q, Int.cast_sub, b] using
      originalNoReturn_near_coordinate_le A B (originalPrivateScale m) hs z w b hb hnear
  have he : (k : ℝ) - originalQuadraticScale m * b ^ 2 =
      -b * originalPrivateScale m * (y - (t - originalPrivateScale m * b)) +
        originalMaskError n * (q : ℝ) := by
    dsimp [k, p, q, y, t, b, originalMaskError]
    push_cast
    rw [translatedConeFrequency_coordinates, translatedConeFrequency_coordinates]
    rw [← originalPrivateScale_sq]
    field_simp
    ring
  have hdist : |(k : ℝ) - originalQuadraticScale m * b ^ 2| ≤
      originalPrivateScale m / b ^ 3 +
        |originalMaskError n| * originalNoReturnCoordinateConstant A B (originalPrivateScale m) z * b := by
    rw [he]
    calc
      _ ≤ |-b * originalPrivateScale m * (y - (t - originalPrivateScale m * b))| +
          |originalMaskError n * (q : ℝ)| := abs_add_le _ _
      _ = b * originalPrivateScale m * |y - (t - originalPrivateScale m * b)| +
          |originalMaskError n| * |(q : ℝ)| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos hbpos, abs_of_pos hs, abs_mul]
      _ ≤ b * originalPrivateScale m * (1 / b ^ 4) +
          |originalMaskError n| *
            (originalNoReturnCoordinateConstant A B (originalPrivateScale m) z * b) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hnear (by positivity))
          (mul_le_mul_of_nonneg_left hq (abs_nonneg _))
      _ = _ := by field_simp
  have hquad := originalQuadratic_integer_distance_lower m (denominator (n + 1) ^ 2)
    hm (pow_pos (denominator_pos (n + 1)) 2) k
  simp only [Nat.cast_pow] at hquad
  have hupper := mul_le_mul_of_nonneg_left hdist
    (show 0 ≤ (2 * originalQuadraticScale m + 1) * b ^ 2 by
      have h := originalQuadraticScale_pos m hm; positivity)
  apply hquad.trans
  convert! hupper using 1
  dsimp [b]
  field_simp

/-- TRUE eventual exclusion of ALL cone points from the quartic physical return window. -/
theorem originalNoReturn_physical_window_empty (A B : ℤ) (m : ℕ) (hm : 0 < m)
    (z : Bool × (ℕ × ℕ)) :
    ∀ᶠ n in atTop, ∀ w : Bool × (ℕ × ℕ),
      1 / (denominator (n + 1) : ℝ) ^ 4 <
        |translatedConeFrequency A B w / originalPrivateScale m -
          (translatedConeFrequency A B z / originalPrivateScale m -
            originalPrivateScale m * (denominator (n + 1) : ℝ))| := by
  have hi : Tendsto (fun n => (denominator (n + 1) : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp denominator_succ_tendsto_atTop
  have hl : Tendsto (fun n => (2 * originalQuadraticScale m + 1) *
      (originalPrivateScale m / (denominator (n + 1) : ℝ) +
        originalNoReturnCoordinateConstant A B (originalPrivateScale m) z *
          ((denominator (n + 1) : ℝ) ^ 3 * |originalMaskError n|))) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      ((hi.const_mul (originalPrivateScale m)).add
        ((originalMaskError_polynomial_tendsto_zero 3).const_mul
          (originalNoReturnCoordinateConstant A B (originalPrivateScale m) z))).const_mul
        (2 * originalQuadraticScale m + 1)
  filter_upwards [hl.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hn w
  by_contra hnot
  have hnear := le_of_not_gt hnot
  exact (not_le_of_gt hn) (originalNoReturn_near_obstruction A B m hm z w n hnear)

end
end MeyerGeneralProblem.StrongParity
