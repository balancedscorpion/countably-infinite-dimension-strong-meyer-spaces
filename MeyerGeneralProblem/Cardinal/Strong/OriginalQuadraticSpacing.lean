module

public import MeyerGeneralProblem.Cardinal.Strong.PrivateOriginalDeletions
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-!
# Actual quadratic Diophantine spacing of the private scale

The square of c*m is literally m²*sqrt(2). Its distance from every
integer has a quantitative reciprocal bound, proved by the nonzero
integer norm, with no badly-approximable certificate assumed.
-/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The literal square of the private physical scale. -/
def originalQuadraticScale (m : ℕ) : ℝ := (m : ℝ) ^ 2 * Real.sqrt 2

theorem originalPrivateScale_sq (m : ℕ) :
    originalPrivateScale m ^ 2 = originalQuadraticScale m := by
  simp only [originalPrivateScale, mul_pow, parityDilationUnit_sq, originalQuadraticScale]
  ring

theorem originalQuadraticScale_pos (m : ℕ) (hm : 0 < m) :
    0 < originalQuadraticScale m := by
  unfold originalQuadraticScale
  positivity

/-- The actual quadratic integer norm is nonzero for every positive scale and return. -/
theorem originalQuadratic_integerNorm_ne_zero (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (k : ℤ) : k ^ 2 - 2 * (((m : ℤ) ^ 2 * (n : ℤ)) ^ 2) ≠ 0 := by
  let v : ℤ := (m : ℤ) ^ 2 * (n : ℤ)
  have hv : v ≠ 0 := by dsimp [v]; positivity
  have hirr : Irrational ((v : ℝ) * Real.sqrt 2) := irrational_sqrt_two.intCast_mul hv
  intro he
  have heR : (k : ℝ) ^ 2 = ((v : ℝ) * Real.sqrt 2) ^ 2 := by
    have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have he' : (k : ℝ) ^ 2 - 2 * (v : ℝ) ^ 2 = 0 := by exact_mod_cast he
    rw [mul_pow, hs]
    nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp heR with heq | heq
  · exact hirr.ne_int k heq.symm
  · apply hirr.ne_int (-k)
    push_cast
    linarith

/-- Quantitative integer-norm bound on the full real line, not merely nearest integers. -/
theorem originalQuadratic_integer_distance_lower (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (k : ℤ) :
    1 ≤ ((2 * originalQuadraticScale m + 1) * (n : ℝ)) *
      |(k : ℝ) - originalQuadraticScale m * (n : ℝ)| := by
  let d : ℝ := |(k : ℝ) - originalQuadraticScale m * (n : ℝ)|
  have hd : 0 ≤ d := abs_nonneg _
  have htheta := originalQuadraticScale_pos m hm
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hbig : 1 ≤ d
  · have ha : 1 ≤ (2 * originalQuadraticScale m + 1) * (n : ℝ) := by
      nlinarith [mul_nonneg htheta.le (show (0 : ℝ) ≤ n by positivity)]
    exact le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1)
      (mul_le_mul ha hbig (by norm_num) (by positivity))
  · have hsmall : d < 1 := lt_of_not_ge hbig
    let z : ℤ := k ^ 2 - 2 * (((m : ℤ) ^ 2 * (n : ℤ)) ^ 2)
    have hz : z ≠ 0 := originalQuadratic_integerNorm_ne_zero m n hm hn k
    have habsz : (1 : ℝ) ≤ |(z : ℝ)| := by
      have hz' : (1 : ℤ) ≤ |z| := by
        have ha := abs_pos.mpr hz
        omega
      exact_mod_cast hz'
    have hnorm : |(z : ℝ)| = d * |(k : ℝ) + originalQuadraticScale m * (n : ℝ)| := by
      dsimp [z, d, originalQuadraticScale]
      push_cast
      rw [← abs_mul]
      congr 1
      have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      nlinarith [sq_nonneg ((m : ℝ) ^ 2 * (n : ℝ))]
    have hk : |(k : ℝ)| ≤ d + originalQuadraticScale m * (n : ℝ) := by
      have h := abs_add_le ((k : ℝ) - originalQuadraticScale m * (n : ℝ))
        (originalQuadraticScale m * (n : ℝ))
      rw [sub_add_cancel, abs_of_pos (mul_pos htheta (by exact_mod_cast hn))] at h
      exact h
    have hplus : |(k : ℝ) + originalQuadraticScale m * (n : ℝ)| ≤
        (2 * originalQuadraticScale m + 1) * (n : ℝ) := by
      have h := abs_add_le (k : ℝ) (originalQuadraticScale m * (n : ℝ))
      rw [abs_of_pos (mul_pos htheta (by exact_mod_cast hn))] at h
      nlinarith
    rw [hnorm] at habsz
    calc
      _ ≤ d * |(k : ℝ) + originalQuadraticScale m * (n : ℝ)| := habsz
      _ ≤ d * ((2 * originalQuadraticScale m + 1) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hplus hd
      _ = _ := by ring

end
end MeyerGeneralProblem.StrongParity
