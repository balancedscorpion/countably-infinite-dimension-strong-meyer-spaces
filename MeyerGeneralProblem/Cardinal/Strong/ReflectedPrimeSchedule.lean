module

public import MeyerGeneralProblem.Cardinal.Strong.PrivatePrimeSchedule

@[expose] public section

/-!
# Literal reflected bandwidth at every searched private block

The original floor program bounds the whole order by its predecessor square.
A fixed additional window floor then pays the reflected inequality
`lambda^2 > 200*s` for EVERY selected block, while preserving both escapes
and all prime/order guarantees. Adaptive dual-certificate window bounds remain
an input at this intermediate interface.
-/

namespace MeyerGeneralProblem.StrongParity

/-- The whole least cubical order has a quadratic bound at every scale at least four. -/
theorem originalPrivateOrder_square_le (m : ℕ) (hm : 4 ≤ m) :
    originalPrivateOrder m ^ 2 ≤ 2 * m ^ 3 := by
  have hs := originalPrivateOrder_pos m (by omega)
  have hp := originalPrivateOrder_pred_square_lt m hm
  have ht : 2 * (originalPrivateOrder m - 1) ≤
      (originalPrivateOrder m - 1) ^ 2 + 1 := by
    simpa only [mul_one, one_pow] using two_mul_le_add_sq (originalPrivateOrder m - 1) 1
  have he : originalPrivateOrder m = (originalPrivateOrder m - 1) + 1 := by omega
  rw [he]
  nlinarith

/-- A sufficient ordinary integer threshold pays the strict reflected bandwidth. -/
theorem originalPrivateOrder_bandwidth (m : ℕ) (hm : 80000 < m) :
    200 * originalPrivateOrder m < m ^ 2 := by
  have hs := originalPrivateOrder_square_le m (by omega)
  by_contra hn
  have hb : m ^ 2 ≤ 200 * originalPrivateOrder m := by omega
  have hsq := pow_le_pow_left' hb 2
  have hmul := Nat.mul_le_mul_left 40000 hs
  have hstrict := Nat.mul_lt_mul_of_pos_right hm (pow_pos (by omega : 0 < m) 3)
  have he : m ^ 4 < m ^ 4 := calc
    m ^ 4 = (m ^ 2) ^ 2 := by ring
    _ ≤ (200 * originalPrivateOrder m) ^ 2 := hsq
    _ = 40000 * originalPrivateOrder m ^ 2 := by ring
    _ ≤ 40000 * (2 * m ^ 3) := hmul
    _ = 80000 * m ^ 3 := by ring
    _ < m * m ^ 3 := hstrict
    _ = m ^ 4 := by ring
  exact (lt_irrefl _) he

/-- Ordinary bounds include the fixed floor that also ensures reflected bandwidth. -/
def originalReflectedWindowBounds (bound : ℕ → ℕ) (n : ℕ) : ℕ := max (bound n) 6

/-- The actual reflected prime program uses the same internally terminating search. -/
abbrev originalReflectedPrimeSchedule (bound : ℕ → ℕ) :=
  originalPrivatePrimeSchedule (originalReflectedWindowBounds bound)

/-- The actual reflected order is the same least cubical integer search. -/
abbrev originalReflectedOrderSchedule (bound : ℕ → ℕ) :=
  originalPrivateOrderSchedule (originalReflectedWindowBounds bound)

/-- Every selected reflected prime exceeds the sufficient bandwidth threshold. -/
theorem originalReflectedPrimeSchedule_large (bound : ℕ → ℕ) (n : ℕ) :
    80000 < originalReflectedPrimeSchedule bound n := by
  change 80000 < originalPrivatePrimeSchedule (originalReflectedWindowBounds bound) n
  have ht := originalPrivatePrimeSchedule_threshold (originalReflectedWindowBounds bound) n
  have hp := pow_le_pow_left'
    (Nat.add_le_add_right (le_max_right (bound n) 6) 1) 3
  dsimp [originalPrivateScaleThreshold, originalReflectedWindowBounds] at ht
  norm_num at hp
  omega

/-- The genuine real private scale of the internally selected reflected block. -/
noncomputable abbrev originalReflectedBlockScale (bound : ℕ → ℕ) :=
  originalPrivateBlockScale (originalReflectedWindowBounds bound)

/-- EVERY actual reflected scale satisfies the literal strict bandwidth inequality. -/
theorem originalReflectedBlockScale_bandwidth (bound : ℕ → ℕ) (n : ℕ) :
    200 * (originalReflectedOrderSchedule bound n : ℝ) <
      originalReflectedBlockScale bound n ^ 2 := by
  have hb : 200 * (originalReflectedOrderSchedule bound n : ℝ) <
      (originalReflectedPrimeSchedule bound n : ℝ) ^ 2 := by
    exact_mod_cast originalPrivateOrder_bandwidth _ (originalReflectedPrimeSchedule_large bound n)
  have hc := mul_le_mul_of_nonneg_right parityDilationUnit_one_le
    (by positivity : 0 ≤ (originalReflectedPrimeSchedule bound n : ℝ))
  dsimp [originalReflectedBlockScale, originalPrivateBlockScale]
  exact hb.trans_le (pow_le_pow_left₀ (by positivity) (by simpa only [one_mul] using hc) 2)

/-- The whole reflected schedule keeps increasing odd primes and the exact literal floor. -/
theorem originalReflectedSchedule_spec (bound : ℕ → ℕ) (n : ℕ) :
    Nat.Prime (originalReflectedPrimeSchedule bound n) ∧
      Odd (originalReflectedPrimeSchedule bound n) ∧
      2 ≤ originalReflectedOrderSchedule bound n ∧
      n ≤ originalReflectedOrderSchedule bound n ∧
      ⌊(originalReflectedOrderSchedule bound n : ℝ) ^ ((3 : ℝ) / 4) / parityDilationUnit⌋₊ =
        originalReflectedPrimeSchedule bound n :=
  ⟨originalPrivatePrimeSchedule_prime _ _, originalPrivatePrimeSchedule_odd _ _,
    originalPrivateOrderSchedule_two_le _ _, originalPrivateOrderSchedule_index_le _ _,
    originalPrivateOrderSchedule_floor _ _⟩

/-- BOTH original windows still escape every requested bound, after the added bandwidth floor. -/
theorem originalReflectedSchedule_escape (bound : ℕ → ℕ) (n : ℕ) :
    (bound n : ℝ) + 1 ≤ originalPrivateBlockHeadRadius (originalReflectedWindowBounds bound) n ∧
      (bound n : ℝ) + 1 < originalReflectedBlockScale bound n * nativePhysicalGap := by
  have hle : (bound n : ℝ) ≤ (originalReflectedWindowBounds bound n : ℝ) := by
    exact_mod_cast le_max_left (bound n) 6
  have hadd : (bound n : ℝ) + 1 ≤ (originalReflectedWindowBounds bound n : ℝ) + 1 := by linarith
  exact ⟨hadd.trans (originalPrivateBlockHeadRadius_escape (originalReflectedWindowBounds bound) n),
    hadd.trans_lt (originalPrivateBlock_physicalGap_escape (originalReflectedWindowBounds bound) n)⟩

end MeyerGeneralProblem.StrongParity
