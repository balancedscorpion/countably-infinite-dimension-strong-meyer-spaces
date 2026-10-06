module

public import MeyerGeneralProblem.Cardinal.Strong.RationalQuarticDilation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Prime.Infinite

@[expose] public section

/-!
# Integer search for the literal private-prime floor schedule

The least natural `s` with `2*m^4 ≤ s^3` is found using only natural
arithmetic. For every `m ≥ 4` its upper cubical bound proves the exact
real floor relation used by the original parity carrier. No real equality
test or externally supplied floor certificate enters this search.
-/

namespace MeyerGeneralProblem.StrongParity

/-- The cubical lower threshold is attained by a natural order. -/
theorem originalPrivateOrder_exists (m : ℕ) : ∃ s : ℕ, 2 * m ^ 4 ≤ s ^ 3 := by
  refine ⟨2 * m ^ 4 + 1, ?_⟩
  exact (Nat.le_succ _).trans (le_self_pow₀ (by omega) (by decide : (3 : ℕ) ≠ 0))

/-- Ordinary terminating search for the least order at private scale `m`. -/
def originalPrivateOrder (m : ℕ) : ℕ := Nat.find (originalPrivateOrder_exists m)

theorem originalPrivateOrder_lower (m : ℕ) :
    2 * m ^ 4 ≤ originalPrivateOrder m ^ 3 :=
  Nat.find_spec (originalPrivateOrder_exists m)

theorem originalPrivateOrder_minimal (m t : ℕ) (ht : t < originalPrivateOrder m) :
    t ^ 3 < 2 * m ^ 4 :=
  lt_of_not_ge (Nat.find_min (originalPrivateOrder_exists m) ht)

theorem originalPrivateOrder_pos (m : ℕ) (hm : 0 < m) :
    0 < originalPrivateOrder m := by
  have h := originalPrivateOrder_lower m
  have hp : 0 < m ^ 4 := pow_pos hm _
  by_contra hs
  have hz : originalPrivateOrder m = 0 := by omega
  simp only [hz, zero_pow (by decide : (3 : ℕ) ≠ 0)] at h
  omega

/-- At `m ≥ 4`, the predecessor's square is strictly below `m^3`. -/
theorem originalPrivateOrder_pred_square_lt (m : ℕ) (hm : 4 ≤ m) :
    (originalPrivateOrder m - 1) ^ 2 < m ^ 3 := by
  have hs := originalPrivateOrder_pos m (by omega)
  have hp := originalPrivateOrder_minimal m (originalPrivateOrder m - 1) (by omega)
  by_contra hn
  have hbad : m ^ 3 ≤ (originalPrivateOrder m - 1) ^ 2 := by omega
  have hlo : m ^ 9 ≤ (originalPrivateOrder m - 1) ^ 6 := by
    calc
      m ^ 9 = (m ^ 3) ^ 3 := by ring
      _ ≤ ((originalPrivateOrder m - 1) ^ 2) ^ 3 := pow_le_pow_left' hbad 3
      _ = (originalPrivateOrder m - 1) ^ 6 := by ring
  have hhi : (originalPrivateOrder m - 1) ^ 6 < 4 * m ^ 8 := by
    have h := pow_lt_pow_left₀ hp (Nat.zero_le _) (by decide : (2 : ℕ) ≠ 0)
    calc
      (originalPrivateOrder m - 1) ^ 6 = ((originalPrivateOrder m - 1) ^ 3) ^ 2 := by ring
      _ < (2 * m ^ 4) ^ 2 := h
      _ = 4 * m ^ 8 := by ring
  have hmid : 4 * m ^ 8 ≤ m ^ 9 := by
    calc
      4 * m ^ 8 ≤ m * m ^ 8 := Nat.mul_le_mul_right _ hm
      _ = m ^ 9 := by ring
  exact (not_lt_of_ge hmid) (hlo.trans_lt hhi)

/-- The least integer order remains below the NEXT private-scale threshold. -/
theorem originalPrivateOrder_upper (m : ℕ) (hm : 4 ≤ m) :
    originalPrivateOrder m ^ 3 < 2 * (m + 1) ^ 4 := by
  have hs := originalPrivateOrder_pos m (by omega)
  have hp := originalPrivateOrder_minimal m (originalPrivateOrder m - 1) (by omega)
  have hp2 := originalPrivateOrder_pred_square_lt m hm
  have he : originalPrivateOrder m = (originalPrivateOrder m - 1) + 1 := by omega
  have ht : originalPrivateOrder m - 1 ≤ (originalPrivateOrder m - 1) ^ 2 + 1 := by
    nlinarith
  rw [he]
  nlinarith

/-- The integer search realizes the EXACT floor, with the actual quartic scale. -/
theorem originalPrivateOrder_floor (m : ℕ) (hm : 4 ≤ m) :
    ⌊(originalPrivateOrder m : ℝ) ^ ((3 : ℝ) / 4) / parityDilationUnit⌋₊ = m := by
  have hnonneg : 0 ≤ (originalPrivateOrder m : ℝ) ^ ((3 : ℝ) / 4) /
      parityDilationUnit := div_nonneg (Real.rpow_nonneg (by positivity) _) parityDilationUnit_pos.le
  have hp : ((originalPrivateOrder m : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 =
      (originalPrivateOrder m : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (originalPrivateOrder m : ℝ))]
    norm_num
  have he : ((originalPrivateOrder m : ℝ) ^ ((3 : ℝ) / 4) / parityDilationUnit) ^ 4 =
      (originalPrivateOrder m : ℝ) ^ 3 / 2 := by
    rw [div_pow, hp, parityDilationUnit_fourth]
  have hlo : 2 * (m : ℝ) ^ 4 ≤ (originalPrivateOrder m : ℝ) ^ 3 := by
    exact_mod_cast originalPrivateOrder_lower m
  have hhi : (originalPrivateOrder m : ℝ) ^ 3 < 2 * ((m : ℝ) + 1) ^ 4 := by
    exact_mod_cast originalPrivateOrder_upper m hm
  apply (Nat.floor_eq_iff hnonneg).mpr
  constructor
  · apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) hnonneg
    rw [he]
    linarith
  · apply lt_of_pow_lt_pow_left₀ 4 (by positivity : 0 ≤ (m : ℝ) + 1)
    rw [he]
    linarith

/-- Distinct increasing private scales give strictly increasing integer orders. -/
theorem originalPrivateOrder_strictMonoOn :
    StrictMonoOn originalPrivateOrder {m : ℕ | 4 ≤ m} := by
  intro m hm n _ hmn
  have hhi := originalPrivateOrder_upper m hm
  have hlo := originalPrivateOrder_lower n
  have hpow : (m + 1) ^ 4 ≤ n ^ 4 := pow_le_pow_left' (by omega : m + 1 ≤ n) 4
  apply lt_of_pow_lt_pow_left₀ 3 (Nat.zero_le _)
  exact hhi.trans_le ((Nat.mul_le_mul_left 2 hpow).trans hlo)

/-- A prime above a prescribed natural threshold exists. -/
theorem originalPrivatePrime_exists (B : ℕ) : ∃ m : ℕ, B + 5 ≤ m ∧ Nat.Prime m :=
  Nat.exists_infinite_primes (B + 5)

/-- Ordinary prime search, retaining the complete requested threshold. -/
def originalPrivatePrime (B : ℕ) : ℕ := Nat.find (originalPrivatePrime_exists B)

theorem originalPrivatePrime_spec (B : ℕ) :
    B + 5 ≤ originalPrivatePrime B ∧ Nat.Prime (originalPrivatePrime B) :=
  Nat.find_spec (originalPrivatePrime_exists B)

theorem originalPrivatePrime_odd (B : ℕ) : Odd (originalPrivatePrime B) := by
  have h := originalPrivatePrime_spec B
  exact h.2.odd_of_ne_two (by omega)

end MeyerGeneralProblem.StrongParity
