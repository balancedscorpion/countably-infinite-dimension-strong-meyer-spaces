module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalSparseCharacters
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

/-! The ACTUAL primitive prime rotations at every scheduled common-coordinate
dilation. No prime, coprimality, order or primitive-root certificate is a final
actual-prefix input. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual coordinate dilation is the literal product of ALL other block primes. -/
theorem originalScheduledPrefixCoordinateDilation_eq_other_product (bound : ℕ → ℕ)
    (k : ℕ) (i : Fin k) : originalScheduledPrefixCoordinateDilation bound k i =
      ∏ j ∈ Finset.univ.erase i, originalReflectedPrimeSchedule bound j.val := by
  classical
  apply mul_right_cancel₀ (originalScheduledBlockPrime_pos bound i.val).ne'
  rw [originalScheduledPrefixCoordinateDilation_mul_prime]
  exact (Finset.prod_erase_mul Finset.univ
    (fun j : Fin k => originalReflectedPrimeSchedule bound j.val) (Finset.mem_univ i)).symm

/-- The ACTUAL native dilation is coprime to its own scheduled prime. -/
theorem originalScheduledPrefixCoordinateDilation_coprime (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    Nat.Coprime (originalScheduledPrefixCoordinateDilation bound k i)
      (originalReflectedPrimeSchedule bound i.val) := by
  classical
  rw [originalScheduledPrefixCoordinateDilation_eq_other_product]
  apply Nat.coprime_prod_left_iff.mpr
  intro j hj
  exact originalScheduledBlockPrimes_coprime bound j.val i.val
    (fun he => (Finset.mem_erase.mp hj).1 (Fin.ext he))

/-- Literal exponential primitive root, stored in its actual scheduled prime group. -/
def originalScheduledPrimitiveRoot (bound : ℕ → ℕ) (i : ℕ) :
    rootsOfUnity (originalReflectedPrimeSchedule bound i) ℂ :=
  ⟨Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / (originalReflectedPrimeSchedule bound i)))
    (Complex.exp_ne_zero _), by
      apply (mem_rootsOfUnity _ _).mpr
      apply Units.ext
      exact (Complex.isPrimitiveRoot_exp _ (originalScheduledBlockPrime_pos bound i).ne').pow_eq_one⟩

/-- The actual stored exponential rotation has the full scheduled prime order. -/
theorem originalScheduledPrimitiveRoot_isPrimitive (bound : ℕ → ℕ) (i : ℕ) :
    IsPrimitiveRoot ((originalScheduledPrimitiveRoot bound i).val : ℂ)
      (originalReflectedPrimeSchedule bound i) :=
  Complex.isPrimitiveRoot_exp _ (originalScheduledBlockPrime_pos bound i).ne'

/-- Even AFTER native coordinate dilation, the ACTUAL rotation still has the full prime order. -/
theorem originalScheduledDilatedPrimitiveRoot_isPrimitive (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    IsPrimitiveRoot (((originalScheduledPrimitiveRoot bound i.val).val : ℂ) ^
      originalScheduledPrefixCoordinateDilation bound k i) (originalReflectedPrimeSchedule bound i.val) :=
  (originalScheduledPrimitiveRoot_isPrimitive bound i.val).pow_of_coprime _
    (originalScheduledPrefixCoordinateDilation_coprime bound k i)

/-- EVERY actual prime polygon contains the three distinct rotations required by the proof. -/
theorem originalScheduledBlockPrime_three_le (bound : ℕ → ℕ) (i : ℕ) :
    3 ≤ originalReflectedPrimeSchedule bound i := by
  have h := originalReflectedPrimeSchedule_large bound i
  omega

end
end MeyerGeneralProblem.StrongParity
