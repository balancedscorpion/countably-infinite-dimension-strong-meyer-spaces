module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalHomogeneousPolynomial
public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrimitiveOrbit

@[expose] public section

/-! FULL divisor-orbit avoidance for every ACTUAL scheduled original block on
all nonzero homogeneous coordinate pairs. The actual prime torus, native power
permutation, original parameter bounds and original quarter phase are internal.
No generic-position, pole-splitting or divisor-irreducibility premise is used. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual whole block factor at its literal common-coordinate dilation. -/
def originalScheduledBlockPositivePolynomial (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  ∏ j : Fin (originalReflectedOrderSchedule bound i.val),
    originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
      ((originalScheduledParameterBlock bound i.val).parameter j)

/-- The literal bihomogeneous original block product, including every infinity coefficient. -/
def originalScheduledBlockHomogeneousPolynomial (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (z₀ z₁ w₀ w₁ : ℂ) : ℂ :=
  ∏ j : Fin (originalReflectedOrderSchedule bound i.val),
    originalPositiveSheetHomogeneous (originalScheduledPrefixCoordinateDilation bound k i)
      ((originalScheduledParameterBlock bound i.val).parameter j) z₀ z₁ w₀ w₁

/-- The homogeneous block is EXACTLY the actual original block polynomial on its affine chart. -/
theorem originalScheduledBlockHomogeneousPolynomial_affine (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (Z W : ℂ) : originalScheduledBlockHomogeneousPolynomial bound k i 1 Z 1 W =
      originalPositiveTorusEvaluation Z W (originalScheduledBlockPositivePolynomial bound k i) := by
  simp only [originalScheduledBlockHomogeneousPolynomial, originalScheduledBlockPositivePolynomial,
    map_prod, originalPositiveSheetHomogeneous_affine]

/-- The actual full mixed polynomial is precisely the product of these same whole block factors. -/
theorem originalScheduledPrefixPolynomial_eq_block_product (bound : ℕ → ℕ) (k : ℕ) :
    originalScheduledPrefixPolynomial bound k = ∏ i : Fin k, originalScheduledBlockPositivePolynomial bound k i := rfl

/-- The true bidegree under BOTH homogeneous scalings is paid by ALL original sheets. -/
theorem originalScheduledBlockHomogeneousPolynomial_scale (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (z₀ z₁ w₀ w₁ ρ σ : ℂ) :
    originalScheduledBlockHomogeneousPolynomial bound k i (ρ * z₀) (ρ * z₁) (σ * w₀) (σ * w₁) =
      ρ ^ (originalScheduledPrefixCoordinateDilation bound k i * originalReflectedOrderSchedule bound i.val) *
      σ ^ (originalScheduledPrefixCoordinateDilation bound k i * originalReflectedOrderSchedule bound i.val) *
      originalScheduledBlockHomogeneousPolynomial bound k i z₀ z₁ w₀ w₁ := by
  simp only [originalScheduledBlockHomogeneousPolynomial, originalPositiveSheetHomogeneous_scale,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-- The ACTUAL stored rotation powers preserve the literal native-power substitution exactly. -/
theorem originalScheduledPrimitiveRoot_native_power (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (t : ℕ) (Z : ℂ) :
    ((((originalScheduledPrimitiveRoot bound i.val) ^ t).val : ℂ) * Z) ^
      originalScheduledPrefixCoordinateDilation bound k i =
    (((originalScheduledPrimitiveRoot bound i.val).val : ℂ) ^
      originalScheduledPrefixCoordinateDilation bound k i) ^ t *
      Z ^ originalScheduledPrefixCoordinateDilation bound k i := by
  simp only [rootsOfUnity.coe_pow, Units.val_pow_eq_pow_val, mul_pow, ← pow_mul, Nat.mul_comm]

/-- EVERY actual full original prime-torus divisor orbit has NO common zero on
ALL homogeneous coordinate pairs, with both axes, infinity edges and all four corners.
No orbit, prime, primitive-root, parameter or native-phase certificate is supplied. -/
theorem originalScheduledBlock_full_divisor_orbit_avoids (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (z₀ z₁ w₀ w₁ : ℂ) (hz : z₀ ≠ 0 ∨ z₁ ≠ 0) (hw : w₀ ≠ 0 ∨ w₁ ≠ 0) :
    ∃ g : OriginalScheduledPrimeTorus bound i.val,
      originalScheduledBlockHomogeneousPolynomial bound k i z₀ ((g.1.val : ℂ) * z₁)
        w₀ ((g.2.val : ℂ) * w₁) ≠ 0 := by
  let d := originalScheduledPrefixCoordinateDilation bound k i
  let ξ : ℂ := ((originalScheduledPrimitiveRoot bound i.val).val : ℂ) ^ d
  have hAB : z₀ ^ d ≠ 0 ∨ z₁ ^ d ≠ 0 := hz.imp (pow_ne_zero d) (pow_ne_zero d)
  have hCD : w₀ ^ d ≠ 0 ∨ complexUnitPhase (-1 / 4) * w₁ ^ d ≠ 0 :=
    hw.imp (pow_ne_zero d) (fun h => mul_ne_zero originalQuarterPhase_ne_zero (pow_ne_zero d h))
  obtain ⟨t, u, htu⟩ := originalHomogeneousSheetProduct_primitive_orbit_avoids
    (originalScheduledParameterBlock bound i.val).parameter
    (originalScheduledParameterBlock bound i.val).parameter_bounds
    (originalScheduledDilatedPrimitiveRoot_isPrimitive bound k i)
    (originalScheduledBlockPrime_three_le bound i.val) (z₀ ^ d) (z₁ ^ d) (w₀ ^ d)
    (complexUnitPhase (-1 / 4) * w₁ ^ d) hAB hCD
  let g : OriginalScheduledPrimeTorus bound i.val :=
    ((originalScheduledPrimitiveRoot bound i.val) ^ t.val, (originalScheduledPrimitiveRoot bound i.val) ^ u.val)
  refine ⟨g, ?_⟩
  have he : originalScheduledBlockHomogeneousPolynomial bound k i z₀ ((g.1.val : ℂ) * z₁)
      w₀ ((g.2.val : ℂ) * w₁) =
      ∏ j : Fin (originalReflectedOrderSchedule bound i.val), originalHomogeneousSheet
        ((originalScheduledParameterBlock bound i.val).parameter j) (z₀ ^ d)
        (ξ ^ t.val * z₁ ^ d) (w₀ ^ d) (ξ ^ u.val * (complexUnitPhase (-1 / 4) * w₁ ^ d)) := by
    unfold originalScheduledBlockHomogeneousPolynomial
    apply Finset.prod_congr rfl
    intro j _
    simp only [originalPositiveSheetHomogeneous, g, originalScheduledPrimitiveRoot_native_power]
    dsimp only [d, ξ]
    unfold originalHomogeneousSheet
    ring
  rw [he]
  exact htu

/-- The actual affine chart has the same full prime-orbit avoidance, including both axes. -/
theorem originalScheduledBlock_affine_divisor_orbit_avoids (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (Z W : ℂ) : ∃ g : OriginalScheduledPrimeTorus bound i.val,
      originalPositiveTorusEvaluation ((g.1.val : ℂ) * Z) ((g.2.val : ℂ) * W)
        (originalScheduledBlockPositivePolynomial bound k i) ≠ 0 := by
  obtain ⟨g, hg⟩ := originalScheduledBlock_full_divisor_orbit_avoids bound k i 1 Z 1 W
    (Or.inl one_ne_zero) (Or.inl one_ne_zero)
  exact ⟨g, by simpa only [originalScheduledBlockHomogeneousPolynomial_affine] using hg⟩

end
end MeyerGeneralProblem.StrongParity
