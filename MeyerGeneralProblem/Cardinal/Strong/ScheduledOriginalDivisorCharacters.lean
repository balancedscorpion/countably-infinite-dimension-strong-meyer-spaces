module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalDivisorOrbit

@[expose] public section

/-! EVERY actual prime action fixes every other original whole block polynomial,
on arbitrary affine coordinates and on ALL homogeneous charts. The original
quarter phase survives; no supplied character-invariance certificate is used. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- An actual prime root is trivial at EVERY other actual block's native power. -/
theorem originalScheduledPrimeRoot_other_native_power (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j)
    (ζ : rootsOfUnity (originalReflectedPrimeSchedule bound i.val) ℂ) :
    (ζ.val : ℂ) ^ originalScheduledPrefixCoordinateDilation bound k j = 1 := by
  have hunit := originalRootOfUnity_zpow_dilation _ _ ζ
    (originalScheduledOtherPrime_dvd_coordinateDilation bound k i j hij) 1
  have hn : ζ.val ^ originalScheduledPrefixCoordinateDilation bound k j = 1 := by
    simpa only [mul_one, zpow_natCast] using hunit
  exact congrArg Units.val hn

/-- Each actual prime-torus element fixes every other FULL homogeneous block,
including all infinity/boundary coefficients of the original polynomial. -/
theorem originalScheduledBlockHomogeneousPolynomial_other_character_invariant
    (bound : ℕ → ℕ) (k : ℕ) (i j : Fin k) (hij : i ≠ j)
    (g : OriginalScheduledPrimeTorus bound i.val) (z₀ z₁ w₀ w₁ : ℂ) :
    originalScheduledBlockHomogeneousPolynomial bound k j z₀ ((g.1.val : ℂ) * z₁)
      w₀ ((g.2.val : ℂ) * w₁) =
    originalScheduledBlockHomogeneousPolynomial bound k j z₀ z₁ w₀ w₁ := by
  unfold originalScheduledBlockHomogeneousPolynomial
  apply Finset.prod_congr rfl
  intro l _
  simp only [originalPositiveSheetHomogeneous, mul_pow,
    originalScheduledPrimeRoot_other_native_power bound k i j hij g.1,
    originalScheduledPrimeRoot_other_native_power bound k i j hij g.2, one_mul]

/-- The actual affine native whole block polynomial is fixed by EVERY other prime action. -/
theorem originalScheduledBlockPositivePolynomial_other_character_invariant
    (bound : ℕ → ℕ) (k : ℕ) (i j : Fin k) (hij : i ≠ j)
    (g : OriginalScheduledPrimeTorus bound i.val) (Z W : ℂ) :
    originalPositiveTorusEvaluation ((g.1.val : ℂ) * Z) ((g.2.val : ℂ) * W)
      (originalScheduledBlockPositivePolynomial bound k j) =
    originalPositiveTorusEvaluation Z W (originalScheduledBlockPositivePolynomial bound k j) := by
  rw [← originalScheduledBlockHomogeneousPolynomial_affine,
    ← originalScheduledBlockHomogeneousPolynomial_affine]
  exact originalScheduledBlockHomogeneousPolynomial_other_character_invariant bound k i j hij g 1 Z 1 W

end
end MeyerGeneralProblem.StrongParity
