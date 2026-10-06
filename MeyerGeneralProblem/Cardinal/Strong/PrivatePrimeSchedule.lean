module

public import MeyerGeneralProblem.Cardinal.Strong.PrivatePrimeFloor
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginalLabelledRoots

@[expose] public section

/-!
# Increasing private primes and escaping original block heads

The caller specifies natural protected-window bounds, not primes or floor
certificates. The ordinary recursive searches supply every prime and order.
The literal original physical gap and noncoarse spectral head both escape
the requested windows. The later reflected dual-certificate algorithm still
has to compute those bounds and assemble the complete common carrier.
-/

namespace MeyerGeneralProblem.StrongParity

/-- A sufficient integer threshold for escape of the original smaller head. -/
def originalPrivateScaleThreshold (B : ℕ) : ℕ := 256 * (B + 1) ^ 3

/-- Exact cubical arithmetic gives a quantitative order-to-scale lower bound. -/
theorem originalPrivateOrder_ratio_lower (B m : ℕ)
    (hm : originalPrivateScaleThreshold B ≤ m) :
    8 * (B + 1) * m ≤ originalPrivateOrder m := by
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (Nat.zero_le _)
  calc
    (8 * (B + 1) * m) ^ 3 = (2 * (256 * (B + 1) ^ 3)) * m ^ 3 := by ring
    _ ≤ (2 * m) * m ^ 3 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hm)
    _ = 2 * m ^ 4 := by ring
    _ ≤ originalPrivateOrder m ^ 3 := originalPrivateOrder_lower m

/-- ALL requested window bounds enter the recursive search; previous primes
are also passed into the next threshold, so repetitions are excluded. -/
def originalPrivatePrimeSchedule (bound : ℕ → ℕ) : ℕ → ℕ
  | 0 => originalPrivatePrime (originalPrivateScaleThreshold (bound 0))
  | n + 1 => originalPrivatePrime
      (max (originalPrivatePrimeSchedule bound n) (originalPrivateScaleThreshold (bound (n + 1))))

/-- The actual order found by cubical search at the selected prime. -/
def originalPrivateOrderSchedule (bound : ℕ → ℕ) (n : ℕ) : ℕ :=
  originalPrivateOrder (originalPrivatePrimeSchedule bound n)

theorem originalPrivatePrimeSchedule_prime (bound : ℕ → ℕ) (n : ℕ) :
    Nat.Prime (originalPrivatePrimeSchedule bound n) := by
  cases n with
  | zero => exact (originalPrivatePrime_spec _).2
  | succ n => exact (originalPrivatePrime_spec _).2

theorem originalPrivatePrimeSchedule_threshold (bound : ℕ → ℕ) (n : ℕ) :
    originalPrivateScaleThreshold (bound n) + 5 ≤ originalPrivatePrimeSchedule bound n := by
  cases n with
  | zero => exact (originalPrivatePrime_spec _).1
  | succ n =>
    have h := (originalPrivatePrime_spec
      (max (originalPrivatePrimeSchedule bound n) (originalPrivateScaleThreshold (bound (n + 1))))).1
    have hl := le_max_right (originalPrivatePrimeSchedule bound n)
      (originalPrivateScaleThreshold (bound (n + 1)))
    exact (Nat.add_le_add_right hl 5).trans h

theorem originalPrivatePrimeSchedule_ge_five (bound : ℕ → ℕ) (n : ℕ) :
    5 ≤ originalPrivatePrimeSchedule bound n := by
  have h := originalPrivatePrimeSchedule_threshold bound n
  omega

theorem originalPrivatePrimeSchedule_odd (bound : ℕ → ℕ) (n : ℕ) :
    Odd (originalPrivatePrimeSchedule bound n) :=
  (originalPrivatePrimeSchedule_prime bound n).odd_of_ne_two
    (by have h := originalPrivatePrimeSchedule_ge_five bound n; omega)

theorem originalPrivatePrimeSchedule_strictMono (bound : ℕ → ℕ) :
    StrictMono (originalPrivatePrimeSchedule bound) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := (originalPrivatePrime_spec
    (max (originalPrivatePrimeSchedule bound n) (originalPrivateScaleThreshold (bound (n + 1))))).1
  have hl := le_max_left (originalPrivatePrimeSchedule bound n)
    (originalPrivateScaleThreshold (bound (n + 1)))
  change originalPrivatePrimeSchedule bound n < originalPrivatePrime
    (max (originalPrivatePrimeSchedule bound n) (originalPrivateScaleThreshold (bound (n + 1))))
  omega

theorem originalPrivatePrimeSchedule_injective (bound : ℕ → ℕ) :
    Function.Injective (originalPrivatePrimeSchedule bound) :=
  (originalPrivatePrimeSchedule_strictMono bound).injective

theorem originalPrivateOrderSchedule_strictMono (bound : ℕ → ℕ) :
    StrictMono (originalPrivateOrderSchedule bound) := by
  intro i j hij
  apply originalPrivateOrder_strictMonoOn
  · have h := originalPrivatePrimeSchedule_ge_five bound i
    exact (by omega : 4 ≤ originalPrivatePrimeSchedule bound i)
  · have h := originalPrivatePrimeSchedule_ge_five bound j
    exact (by omega : 4 ≤ originalPrivatePrimeSchedule bound j)
  · exact originalPrivatePrimeSchedule_strictMono bound hij

theorem originalPrivateOrderSchedule_floor (bound : ℕ → ℕ) (n : ℕ) :
    ⌊(originalPrivateOrderSchedule bound n : ℝ) ^ ((3 : ℝ) / 4) / parityDilationUnit⌋₊ =
      originalPrivatePrimeSchedule bound n :=
  originalPrivateOrder_floor _ (by have h := originalPrivatePrimeSchedule_ge_five bound n; omega)

theorem originalPrivateOrderSchedule_ratio_lower (bound : ℕ → ℕ) (n : ℕ) :
    8 * (bound n + 1) * originalPrivatePrimeSchedule bound n ≤
      originalPrivateOrderSchedule bound n :=
  originalPrivateOrder_ratio_lower _ _
    (by have h := originalPrivatePrimeSchedule_threshold bound n; omega)

theorem originalPrivateOrderSchedule_two_le (bound : ℕ → ℕ) (n : ℕ) :
    2 ≤ originalPrivateOrderSchedule bound n := by
  have h := originalPrivateOrderSchedule_ratio_lower bound n
  have hm := originalPrivatePrimeSchedule_ge_five bound n
  nlinarith

/-- No selected index above `N` can have order at most `N`. -/
theorem originalPrivateOrderSchedule_index_le (bound : ℕ → ℕ) (n : ℕ) :
    n ≤ originalPrivateOrderSchedule bound n := by
  have h := (originalPrivateOrderSchedule_strictMono bound).add_le_nat n 0
  simpa only [Nat.add_zero] using (Nat.le_add_right n (originalPrivateOrderSchedule bound 0)).trans h

/-- The finite, ordinarily computable list of ALL orders admitted below `N`. -/
def originalPrivateAdmittedIndices (bound : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => originalPrivateOrderSchedule bound n ≤ N)

theorem originalPrivateAdmittedIndices_mem_iff (bound : ℕ → ℕ) (N n : ℕ) :
    n ∈ originalPrivateAdmittedIndices bound N ↔ originalPrivateOrderSchedule bound n ≤ N := by
  simp only [originalPrivateAdmittedIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    exact ⟨by have hi := originalPrivateOrderSchedule_index_le bound n; omega, h⟩

/-- The literal scale `lambda=c*m` of a selected block. -/
noncomputable def originalPrivateBlockScale (bound : ℕ → ℕ) (n : ℕ) : ℝ :=
  parityDilationUnit * (originalPrivatePrimeSchedule bound n : ℝ)

theorem originalPrivateBlockScale_pos (bound : ℕ → ℕ) (n : ℕ) :
    0 < originalPrivateBlockScale bound n :=
  mul_pos parityDilationUnit_pos
    (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 5) (originalPrivatePrimeSchedule_ge_five bound n)))

/-- The actual smaller spectral radius from the complete original head. -/
noncomputable def originalPrivateBlockHeadRadius (bound : ℕ → ℕ) (n : ℕ) : ℝ :=
  (((originalPrivateOrderSchedule bound n / 2 : ℕ) : ℝ) / 2) /
    originalPrivateBlockScale bound n

/-- The ENTIRE allowed noncoarse head is deleted beyond the requested window. -/
theorem originalPrivateBlockHeadRadius_escape (bound : ℕ → ℕ) (n : ℕ) :
    (bound n : ℝ) + 1 ≤ originalPrivateBlockHeadRadius bound n := by
  have hr := originalPrivateOrderSchedule_ratio_lower bound n
  have hhalf : 4 * (bound n + 1) * originalPrivatePrimeSchedule bound n ≤
      originalPrivateOrderSchedule bound n / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    convert! hr using 1
    ring
  have hhalfR : 4 * ((bound n : ℝ) + 1) * (originalPrivatePrimeSchedule bound n : ℝ) ≤
      ((originalPrivateOrderSchedule bound n / 2 : ℕ) : ℝ) := by exact_mod_cast hhalf
  have hm : 0 ≤ (originalPrivatePrimeSchedule bound n : ℝ) := by positivity
  have hc := mul_le_mul_of_nonneg_right parityDilationUnit_le_two hm
  have hmul := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (bound n : ℝ) + 1)
  apply (le_div_iff₀ (originalPrivateBlockScale_pos bound n)).mpr
  dsimp [originalPrivateBlockScale]
  nlinarith

/-- The original physical gap also escapes EVERY requested window. -/
theorem originalPrivateBlock_physicalGap_escape (bound : ℕ → ℕ) (n : ℕ) :
    (bound n : ℝ) + 1 < originalPrivateBlockScale bound n * nativePhysicalGap := by
  have ht := originalPrivatePrimeSchedule_threshold bound n
  have hm : 256 * ((bound n : ℝ) + 1) ^ 3 + 5 ≤
      (originalPrivatePrimeSchedule bound n : ℝ) := by
    exact_mod_cast ht
  have hb := beta_between_three_four
  have hc := parityDilationUnit_one_le
  have hn : 0 ≤ (originalPrivatePrimeSchedule bound n : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hc hn
  have hB : 1 ≤ (bound n : ℝ) + 1 := by
    have hnB : 0 ≤ (bound n : ℝ) := by positivity
    linarith
  have hpow : (bound n : ℝ) + 1 ≤ ((bound n : ℝ) + 1) ^ 3 :=
    le_self_pow₀ hB (by decide : (3 : ℕ) ≠ 0)
  dsimp [originalPrivateBlockScale, nativePhysicalGap]
  rw [one_div, ← div_eq_mul_inv]
  apply (lt_div_iff₀ (by linarith : 0 < 8 * (1 + beta))).mpr
  nlinarith

end MeyerGeneralProblem.StrongParity
