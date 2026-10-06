module

public import MeyerGeneralProblem.Cardinal.Strong.ParityLimit
public import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions

@[expose] public section

/-!
# Canonical continued fraction of the constructed parity limit

Positive signed continuant errors supply the complete quotients. Their
floors and fractional-part reciprocals identify the canonical continued
fraction of the actual constructed real number, rather than only some
rational approximants to it.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The actual continued-fraction partial quotients, including its head. -/
def partialQuotient : ℕ → ℕ
  | 0 => 3
  | 1 => 1
  | n + 2 => 2 * denominator (n + 1) ^ (n + 2)

/-- The positive signed error of a prescribed continuant. -/
def signedError (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * ((denominator n : ℝ) * beta - numerator n)

theorem signedError_pos (n : ℕ) : 0 < signedError n := by
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn
    have h := convergent_even_lt_beta k
    have hq : (0 : ℝ) < denominator (2 * k) := by
      exact_mod_cast denominator_pos (2 * k)
    rw [convergent, div_lt_iff₀ hq] at h
    simp only [signedError, pow_mul, neg_one_sq, one_pow, one_mul]
    nlinarith
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hn
    have h := beta_lt_convergent_odd k
    have hq : (0 : ℝ) < denominator (2 * k + 1) := by
      exact_mod_cast denominator_pos (2 * k + 1)
    rw [convergent, lt_div_iff₀ hq] at h
    simp only [signedError, pow_add, pow_mul, neg_one_sq, one_pow, pow_one,
      one_mul, neg_one_mul]
    nlinarith

theorem partialQuotient_add_two_ge_two (n : ℕ) : 2 ≤ partialQuotient (n + 2) := by
  change 2 ≤ 2 * denominator (n + 1) ^ (n + 2)
  have h := Nat.one_le_pow (n + 2) (denominator (n + 1)) (denominator_pos (n + 1))
  omega

/-- The positive error recurrence determines all complete-quotient floors. -/
theorem signedError_recurrence (n : ℕ) :
    signedError n = (partialQuotient (n + 2) : ℝ) * signedError (n + 1) +
      signedError (n + 2) := by
  unfold signedError
  rw [numerator_recurrence, denominator_recurrence]
  change _ = ((2 * denominator (n + 1) ^ (n + 2) : ℕ) : ℝ) * _ + _
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
  ring

theorem signedError_succ_lt (n : ℕ) : signedError (n + 1) < signedError n := by
  have h := signedError_recurrence n
  have ha : (2 : ℝ) ≤ partialQuotient (n + 2) := by
    exact_mod_cast partialQuotient_add_two_ge_two n
  nlinarith [signedError_pos (n + 1), signedError_pos (n + 2)]

/-- The actual complete quotients, with the two initial quotients explicit. -/
def completeQuotient : ℕ → ℝ
  | 0 => beta
  | 1 => 1 / (beta - 3)
  | n + 2 => signedError n / signedError (n + 1)

theorem completeQuotient_add_two_bounds (n : ℕ) :
    (partialQuotient (n + 2) : ℝ) < completeQuotient (n + 2) ∧
      completeQuotient (n + 2) < partialQuotient (n + 2) + 1 := by
  change (partialQuotient (n + 2) : ℝ) < signedError n / signedError (n + 1) ∧
    signedError n / signedError (n + 1) < partialQuotient (n + 2) + 1
  rw [lt_div_iff₀ (signedError_pos (n + 1)), div_lt_iff₀ (signedError_pos (n + 1))]
  have h := signedError_recurrence n
  have hs := signedError_succ_lt (n + 1)
  constructor <;> nlinarith [signedError_pos (n + 2)]

theorem completeQuotient_bounds (n : ℕ) :
    (partialQuotient n : ℝ) < completeQuotient n ∧
      completeQuotient n < partialQuotient n + 1 := by
  rcases n with _ | _ | n
  · convert beta_between_three_four using 1 <;>
      norm_num [partialQuotient, completeQuotient]
  · have hlo := convergent_even_le_beta 1
    have hhi := beta_between_three_four.2
    norm_num [convergent, numerator, denominator, continuantPair] at hlo
    norm_num only [partialQuotient, completeQuotient, Nat.cast_one]
    have hp : 0 < beta - 3 := by linarith
    rw [lt_div_iff₀ hp, div_lt_iff₀ hp]
    constructor <;> linarith
  · exact completeQuotient_add_two_bounds n

theorem completeQuotient_floor (n : ℕ) :
    ⌊completeQuotient n⌋ = (partialQuotient n : ℤ) := by
  apply Int.floor_eq_iff.mpr
  have h := completeQuotient_bounds n
  exact ⟨by exact_mod_cast h.1.le, by exact_mod_cast h.2⟩

/-- Each prescribed complete quotient is the reciprocal fractional part
of its predecessor; no termination or coefficient assumption is supplied. -/
theorem completeQuotient_succ (n : ℕ) :
    completeQuotient (n + 1) = (Int.fract (completeQuotient n))⁻¹ := by
  rw [Int.fract, completeQuotient_floor]
  simp only [Int.cast_natCast]
  rcases n with _ | _ | n
  · simp [completeQuotient, partialQuotient, one_div]
  · norm_num only [partialQuotient, completeQuotient, Nat.cast_one]
    have h3 : beta - 3 ≠ 0 := (sub_pos.mpr beta_between_three_four.1).ne'
    have hdiv : 1 / (beta - 3) - 1 = (4 - beta) / (beta - 3) := by
      field_simp
      ring
    rw [hdiv, inv_div]
    norm_num [signedError, denominator, numerator, continuantPair]
  · change signedError (n + 1) / signedError (n + 2) =
      (signedError n / signedError (n + 1) - (partialQuotient (n + 2) : ℝ))⁻¹
    have h := signedError_recurrence n
    have hdiv : signedError n / signedError (n + 1) -
        (partialQuotient (n + 2) : ℝ) = signedError (n + 2) / signedError (n + 1) := by
      rw [h]
      field_simp [(signedError_pos (n + 1)).ne']
      ring
    rw [hdiv, inv_div]


theorem completeQuotient_fract_ne_zero (n : ℕ) :
    Int.fract (completeQuotient n) ≠ 0 := by
  rw [Int.fract, completeQuotient_floor, Int.cast_natCast]
  exact (sub_pos.mpr (completeQuotient_bounds n).1).ne'

/-- Every stage of the canonical algorithm is the actual prescribed
complete quotient, with a nonzero fractional part. -/
theorem canonical_intFractPair_stream (n : ℕ) :
    GenContFract.IntFractPair.stream beta n =
      some (GenContFract.IntFractPair.of (completeQuotient n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [GenContFract.IntFractPair.stream_succ_of_some ih
        (completeQuotient_fract_ne_zero n)]
      change some (GenContFract.IntFractPair.of
        (Int.fract (completeQuotient n))⁻¹) = _
      rw [← completeQuotient_succ]

/-- All canonical partial numerators and denominators are identified. -/
theorem canonical_partial_quotients (n : ℕ) :
    (GenContFract.of beta).s.get? n =
      some ⟨1, (partialQuotient (n + 1) : ℝ)⟩ := by
  have h := GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream
    (canonical_intFractPair_stream (n + 1))
  simpa only [GenContFract.IntFractPair.of, completeQuotient_floor, Int.cast_natCast] using h

/-- The complete canonical continuant sequence is the prescribed sequence,
not merely a subsequence of good rational approximants. -/
theorem canonical_continuants (n : ℕ) :
    (GenContFract.of beta).conts n = ⟨(numerator n : ℝ), (denominator n : ℝ)⟩ := by
  have hf : ⌊beta⌋ = (3 : ℤ) := completeQuotient_floor 0
  induction n using Nat.twoStepInduction with
  | zero =>
      norm_num [GenContFract.zeroth_cont_eq_h_one, GenContFract.of_h_eq_floor,
        hf, numerator, denominator, continuantPair]
  | one =>
      rw [GenContFract.first_cont_eq (canonical_partial_quotients 0)]
      norm_num [partialQuotient, GenContFract.of_h_eq_floor, hf,
        numerator, denominator, continuantPair]
  | more n hn hn1 =>
      rw [GenContFract.conts_recurrence (canonical_partial_quotients (n + 1)) hn hn1]
      rw [numerator_recurrence, denominator_recurrence]
      simp only [partialQuotient, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_pow, one_mul]


/-- Canonical rational convergents have exactly the prescribed values. -/
theorem canonical_rat_convergent (n : ℕ) :
    Real.convergent beta n = (numerator n : ℚ) / denominator n := by
  apply Rat.cast_injective (α := ℝ)
  rw [← Real.convs_eq_convergent]
  push_cast
  rw [GenContFract.conv_eq_conts_a_div_conts_b, canonical_continuants]

/-- The denominator equality uses actual reduced fractions and the already
proved coprimality, so parity cannot be lost in a normalization step. -/
theorem canonical_convergent_denominator (n : ℕ) :
    (Real.convergent beta n).den = denominator n := by
  rw [canonical_rat_convergent]
  have h := Rat.den_div_eq_of_coprime
    (show (0 : ℤ) < denominator n by exact_mod_cast denominator_pos n)
    (show Nat.Coprime (numerator n : ℤ).natAbs (denominator n : ℤ).natAbs by
      simpa only [Int.natAbs_natCast] using numerator_denominator_coprime n)
  have hZ : (((numerator n : ℚ) / denominator n).den : ℤ) = (denominator n : ℤ) := by
    simpa only [Int.cast_natCast] using h
  exact Int.natCast_inj.mp hZ

theorem canonical_convergent_denominator_odd (n : ℕ) :
    Odd (Real.convergent beta n).den := by
  rw [canonical_convergent_denominator]
  exact denominator_odd n

end

end MeyerGeneralProblem.StrongParity
