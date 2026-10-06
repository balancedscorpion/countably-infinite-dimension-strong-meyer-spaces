module

public import MeyerGeneralProblem.Cardinal.Strong.CanonicalContinuants
public import Mathlib.Algebra.Ring.Int.Parity

@[expose] public section

/-!
# The original inhomogeneous parity barrier

The canonical convergents of the constructed Liouville real number have
odd reduced denominators. An odd numerator divided by twice a nonzero
integer has even reduced denominator. Legendre's criterion therefore
excludes excessively accurate approximations of the original odd phase.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Reducing an odd numerator over an even nonzero denominator preserves
an even denominator, including negative denominators. -/
theorem odd_numerator_even_reduced_denominator {u k : ℤ} (hu : Odd u) (hk : k ≠ 0) :
    Even (Rat.divInt u (2 * k)).den := by
  apply Nat.not_odd_iff_even.mp
  intro hd
  let q : ℚ := Rat.divInt u (2 * k)
  obtain ⟨c, hcNum, hcDen⟩ := Rat.num_den_mk
    (mul_ne_zero (by decide : (2 : ℤ) ≠ 0) hk) (show q = Rat.divInt u (2 * k) from rfl)
  have hc : Odd c := Int.Odd.of_mul_left (hcNum ▸ hu)
  have hdInt : Odd (q.den : ℤ) := Odd.natCast hd
  have hodd : Odd (2 * k) := hcDen ▸ hc.mul hdInt
  exact (Int.not_even_iff_odd.mpr hodd) (even_two.mul_right k)

/-- The reduced denominator never exceeds the original absolute denominator. -/
theorem reduced_denominator_le_twice_abs {u k : ℤ} (hk : k ≠ 0) :
    ((Rat.divInt u (2 * k)).den : ℝ) ≤ 2 * |(k : ℝ)| := by
  have hd := Int.natCast_dvd.mp (Rat.den_dvd u (2 * k))
  have hpos : 0 < (2 * k).natAbs := Int.natAbs_pos.mpr
    (mul_ne_zero (by decide : (2 : ℤ) ≠ 0) hk)
  have hle := Nat.le_of_dvd hpos hd
  have hleR : (((Rat.divInt u (2 * k)).den : ℕ) : ℝ) ≤ ((2 * k).natAbs : ℝ) := by
    exact_mod_cast hle
  norm_num only [Nat.cast_natAbs, Int.cast_abs, Int.cast_mul,
    Int.cast_ofNat, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hleR
  exact hleR

/-- The quantitative lower bound used for the original strong mass estimates. -/
theorem parity_barrier {k u : ℤ} (hk : k ≠ 0) (hu : Odd u) :
    1 / (4 * |(k : ℝ)|) ≤ |2 * (k : ℝ) * beta - u| := by
  by_contra! hsmall
  let q : ℚ := Rat.divInt u (2 * k)
  have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hkabs : 0 < |(k : ℝ)| := abs_pos.mpr hkR
  have hdenpos : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hdenle : (q.den : ℝ) ≤ 2 * |(k : ℝ)| := reduced_denominator_le_twice_abs hk
  have hcast : (q : ℝ) = u / (2 * (k : ℝ)) := by
    simp only [q, Rat.cast_divInt, Int.cast_mul, Int.cast_ofNat]
  have herror : |beta - (q : ℝ)| = |2 * (k : ℝ) * beta - u| / (2 * |(k : ℝ)|) := by
    rw [hcast]
    have hid : beta - (u : ℝ) / (2 * (k : ℝ)) =
        (2 * (k : ℝ) * beta - u) / (2 * (k : ℝ)) := by field_simp
    rw [hid, abs_div, abs_mul]
    norm_num
  have hlegendre : |beta - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2) := by
    rw [herror]
    calc
      _ < (1 / (4 * |(k : ℝ)|)) / (2 * |(k : ℝ)|) :=
        (div_lt_div_iff_of_pos_right (by positivity)).mpr hsmall
      _ = 1 / (8 * |(k : ℝ)| ^ 2) := by field_simp; norm_num
      _ ≤ 1 / (2 * (q.den : ℝ) ^ 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
  obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent hlegendre
  have hodd : Odd q.den := hn ▸ canonical_convergent_denominator_odd n
  have heven : Even q.den := odd_numerator_even_reduced_denominator hu hk
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end

end MeyerGeneralProblem.StrongParity
