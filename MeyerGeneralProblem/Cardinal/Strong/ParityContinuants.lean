module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Continuants of the explicit parity-Liouville construction

`PARITY_SOLVER.md` Section 1 fixes `[3; 1, a₂, ...]` with
`aⱼ = 2 qⱼ₋₁ ^ j`. The state below stores two consecutive numerator and
denominator pairs, starting with `(3,1)` and `(4,1)`.

This module proves arithmetic facts about this actual recurrence. Identifying
its limit with a real continued fraction, its Liouville estimates and its
inhomogeneous parity bound are separate obligations.
-/

namespace MeyerGeneralProblem.StrongParity

/-- Consecutive `(pₙ,qₙ)` and `(pₙ₊₁,qₙ₊₁)` of the prescribed recurrence. -/
def continuantPair : ℕ → (ℕ × ℕ) × (ℕ × ℕ)
  | 0 => ((3, 1), (4, 1))
  | n + 1 =>
      let s := continuantPair n
      let a := 2 * s.2.2 ^ (n + 2)
      (s.2, (a * s.2.1 + s.1.1, a * s.2.2 + s.1.2))

/-- The actual numerator at index `n`, beginning with `p₀=3`. -/
def numerator (n : ℕ) : ℕ := (continuantPair n).1.1

/-- The actual denominator at index `n`, beginning with `q₀=q₁=1`. -/
def denominator (n : ℕ) : ℕ := (continuantPair n).1.2

@[simp]
theorem numerator_succ (n : ℕ) :
    numerator (n + 1) = (continuantPair n).2.1 := rfl

@[simp]
theorem denominator_succ (n : ℕ) :
    denominator (n + 1) = (continuantPair n).2.2 := rfl

/-- This is the stated partial quotient `aₙ₊₂`, not a supplied sequence. -/
theorem numerator_recurrence (n : ℕ) :
    numerator (n + 2) =
      2 * denominator (n + 1) ^ (n + 2) * numerator (n + 1) + numerator n := rfl

theorem denominator_recurrence (n : ℕ) :
    denominator (n + 2) =
      2 * denominator (n + 1) ^ (n + 2) * denominator (n + 1) + denominator n := rfl

theorem continuantPair_denominators_pos (n : ℕ) :
    0 < (continuantPair n).1.2 ∧ 0 < (continuantPair n).2.2 := by
  induction n with
  | zero => norm_num [continuantPair]
  | succ n ih =>
      constructor
      · exact ih.2
      · change 0 < 2 * (continuantPair n).2.2 ^ (n + 2) *
          (continuantPair n).2.2 + (continuantPair n).1.2
        exact ih.1.trans_le (Nat.le_add_left _ _)

theorem denominator_pos (n : ℕ) : 0 < denominator n :=
  (continuantPair_denominators_pos n).1

/-- Every denominator is odd despite the very large even partial quotients. -/
theorem continuantPair_denominators_odd (n : ℕ) :
    Odd (continuantPair n).1.2 ∧ Odd (continuantPair n).2.2 := by
  induction n with
  | zero => norm_num [continuantPair]
  | succ n ih =>
      constructor
      · exact ih.2
      · change Odd (2 * (continuantPair n).2.2 ^ (n + 2) *
          (continuantPair n).2.2 + (continuantPair n).1.2)
        exact (even_two.mul_right _ |>.mul_right _).add_odd ih.1

theorem denominator_odd (n : ℕ) : Odd (denominator n) :=
  (continuantPair_denominators_odd n).1

/-- The denominators have the precise super-power growth used by the
Liouville estimates; the positive earlier denominator is retained. -/
theorem denominator_growth (n : ℕ) :
    2 * denominator (n + 1) ^ (n + 3) < denominator (n + 2) := by
  rw [denominator_recurrence]
  have hp := denominator_pos n
  have he : 2 * denominator (n + 1) ^ (n + 2) * denominator (n + 1) =
      2 * denominator (n + 1) ^ (n + 3) := by
    rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
    ring
  rw [he]
  omega

/-- Each step after the initial pair more than doubles the denominator. -/
theorem denominator_succ_double (n : ℕ) :
    2 * denominator (n + 1) < denominator (n + 2) := by
  have hpow := le_self_pow (show 1 ≤ denominator (n + 1) by
    exact denominator_pos (n + 1)) (show n + 3 ≠ 0 by omega)
  exact (Nat.mul_le_mul_left 2 hpow).trans_lt (denominator_growth n)

theorem denominator_monotone : Monotone denominator := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => norm_num [denominator, continuantPair]
  | succ n =>
      have h := denominator_succ_double n
      change denominator (n + 1) ≤ denominator (n + 2)
      omega

/-- A geometric lower bound sufficient for absolute convergence of the
reciprocal determinant increments. -/
theorem denominator_ge_two_pow (n : ℕ) :
    2 ^ n ≤ denominator (n + 1) := by
  induction n with
  | zero => norm_num [denominator, continuantPair]
  | succ n ih =>
      have h := denominator_succ_double n
      rw [pow_succ]
      change 2 ^ n * 2 ≤ denominator (n + 2)
      nlinarith

/-- The determinant has its original alternating sign. In particular, no
large common factor can enter either rational convergent. -/
theorem continuantPair_determinant (n : ℕ) :
    ((continuantPair n).2.1 : ℤ) * (continuantPair n).1.2 -
      ((continuantPair n).1.1 : ℤ) * (continuantPair n).2.2 = (-1 : ℤ) ^ n := by
  induction n with
  | zero => norm_num [continuantPair]
  | succ n ih =>
      simp only [continuantPair, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      calc
        _ = - (((continuantPair n).2.1 : ℤ) * (continuantPair n).1.2 -
          ((continuantPair n).1.1 : ℤ) * (continuantPair n).2.2) := by ring
        _ = (-1 : ℤ) ^ (n + 1) := by rw [ih, pow_succ]; ring

/-- Each original continuant is already a reduced rational fraction. -/
theorem numerator_denominator_coprime (n : ℕ) :
    Nat.Coprime (numerator n) (denominator n) := by
  have hd := continuantPair_determinant n
  change (numerator (n + 1) : ℤ) * denominator n -
    (numerator n : ℤ) * denominator (n + 1) = (-1 : ℤ) ^ n at hd
  have hs : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hc : IsCoprime (numerator n : ℤ) (denominator n : ℤ) := by
    refine ⟨-((-1 : ℤ) ^ n * denominator (n + 1)),
      (-1 : ℤ) ^ n * numerator (n + 1), ?_⟩
    calc
      _ = (-1 : ℤ) ^ n * ((numerator (n + 1) : ℤ) * denominator n -
          (numerator n : ℤ) * denominator (n + 1)) := by ring
      _ = 1 := by rw [hd, hs]
  simpa only [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast] using hc

/-- Consecutive numerators have opposite parity. -/
theorem continuantPair_numerator_parities (n : ℕ) :
    (continuantPair n).1.1 % 2 + (continuantPair n).2.1 % 2 = 1 := by
  induction n with
  | zero => norm_num [continuantPair]
  | succ n ih =>
      simpa [continuantPair, Nat.add_mod, Nat.mul_mod, Nat.add_comm] using ih

/-- Choose the actual `rⱼ ∈ {1,3}` in the quarter-phase construction. -/
def quarterMultiplier (qPrev q : ℕ) : ℕ :=
  if qPrev % 4 = q % 4 then 3 else 1

theorem quarterMultiplier_values (qPrev q : ℕ) :
    quarterMultiplier qPrev q = 1 ∨ quarterMultiplier qPrev q = 3 := by
  unfold quarterMultiplier
  split <;> simp

/-- Odd consecutive denominators produce a genuine quarter denominator. -/
theorem quarterMultiplier_denominator_mod_four {qPrev q : ℕ}
    (hPrev : Odd qPrev) (hq : Odd q) :
    (quarterMultiplier qPrev q * q + qPrev) % 4 = 0 := by
  have hp := Nat.odd_iff.mp hPrev
  have hc := Nat.odd_iff.mp hq
  unfold quarterMultiplier
  split <;> omega

/-- The same chosen quarter combination has an odd numerator, using the
opposite numerator parities rather than a substituted torus phase. -/
theorem quarter_combination_numerator_odd (n : ℕ) :
    Odd (quarterMultiplier (denominator n) (denominator (n + 1)) *
      numerator (n + 1) + numerator n) := by
  apply Nat.odd_iff.mpr
  have hp := continuantPair_numerator_parities n
  have hr : quarterMultiplier (denominator n) (denominator (n + 1)) % 2 = 1 := by
    rcases quarterMultiplier_values (denominator n) (denominator (n + 1)) with h | h
    · rw [h]
    · rw [h]
  change numerator n % 2 + numerator (n + 1) % 2 = 1 at hp
  rw [Nat.add_mod, Nat.mul_mod, hr, one_mul, Nat.mod_mod, Nat.add_comm, hp]

end MeyerGeneralProblem.StrongParity
