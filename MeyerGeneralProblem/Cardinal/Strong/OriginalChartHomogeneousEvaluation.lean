module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalChartBlocks

@[expose] public section

/-! Literal original homogeneous evaluation on every native chart, with the
quarter phase AFTER powers. All complex coordinate values, axes and corners
are included. Acting on a reversed chart inverts precisely that torus coordinate. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- First homogeneous coordinate of one actual affine or infinity chart. -/
def originalChartHomogeneousZero (reverse : Bool) (z : ℂ) : ℂ := if reverse then z else 1

/-- Second homogeneous coordinate of that same actual chart. -/
def originalChartHomogeneousOne (reverse : Bool) (z : ℂ) : ℂ := if reverse then 1 else z

/-- EVERY complex chart coordinate gives a nonzero homogeneous coordinate pair. -/
theorem originalChartHomogeneous_nonzero (b : Bool) (z : ℂ) :
    originalChartHomogeneousZero b z ≠ 0 ∨ originalChartHomogeneousOne b z ≠ 0 := by
  cases b <;> simp [originalChartHomogeneousZero, originalChartHomogeneousOne]

/-- Every literal original phased native sheet evaluates exactly on ALL four charts,
including degree zero and coefficient collisions; there is no phase certificate. -/
theorem originalPositiveSheetHomogeneous_chart_character_eval (c : Bool × Bool) (d : ℕ) (a : ℝ)
    (ζ η : ℂˣ) (Z W : ℂ) :
    originalPositiveSheetHomogeneous d a (originalChartHomogeneousZero c.1 Z)
      ((ζ : ℂ) * originalChartHomogeneousOne c.1 Z) (originalChartHomogeneousZero c.2 W)
      ((η : ℂ) * originalChartHomogeneousOne c.2 W) =
    originalPositiveTorusEvaluation Z W (originalPositiveChartReflection c d
      (originalPositiveCharacterTwist (originalIntegerTorusCharacter ζ η) (originalPositiveSheetPolynomial d a))) := by
  rw [← originalPhasedPositiveSheetPolynomial_original, originalPositiveCharacterTwist_phased_sheet]
  rcases c with ⟨b, e⟩
  cases b <;> cases e <;>
    simp only [originalPositiveSheetHomogeneous, originalHomogeneousSheet,
      originalChartHomogeneousZero, originalChartHomogeneousOne, Bool.false_eq_true, ite_true, ite_false,
      originalPhasedPositiveSheetPolynomial, map_sub, map_add, originalPositiveChartReflection_single,
      originalChartNativeIndex, originalPositiveTorusEvaluation_single, Nat.sub_self, Nat.sub_zero,
      pow_zero, one_pow, mul_pow, one_mul, mul_one] <;> ring

/-- The genuine whole original character block reflects as ALL its literal native sheet factors. -/
theorem originalScheduledBlock_chart_character_product (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalPositiveChartReflection c (originalScheduledChartBlockDegree bound k i)
      (originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
        (originalScheduledBlockPositivePolynomial bound k i)) =
    ∏ j : Fin (originalReflectedOrderSchedule bound i.val),
      originalPositiveChartReflection c (originalScheduledPrefixCoordinateDilation bound k i)
        (originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
          (originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
            ((originalScheduledParameterBlock bound i.val).parameter j))) := by
  unfold originalScheduledBlockPositivePolynomial
  rw [map_prod]
  have h := originalPositiveChartReflection_prod c Finset.univ
    (fun j : Fin (originalReflectedOrderSchedule bound i.val) =>
      originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
        (originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
          ((originalScheduledParameterBlock bound i.val).parameter j)))
    (fun _ => originalScheduledPrefixCoordinateDilation bound k i)
    (fun j _ => by
      apply originalPositiveInSquare_twist
      rw [← originalPhasedPositiveSheetPolynomial_original]
      exact originalPhasedPositiveSheetPolynomial_inSquare _ _ _ _)
  simpa [originalScheduledChartBlockDegree] using h

/-- The original homogeneous whole-block action is the EXACT chart polynomial action,
with its literal degree scalar and internally transported private torus. -/
theorem originalScheduledBlockHomogeneousPolynomial_chart_character_eval (c : Bool × Bool)
    (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) (Z W : ℂ) :
    originalScheduledBlockHomogeneousPolynomial bound k i (originalChartHomogeneousZero c.1 Z)
      ((g.1.val : ℂ) * originalChartHomogeneousOne c.1 Z) (originalChartHomogeneousZero c.2 W)
      ((g.2.val : ℂ) * originalChartHomogeneousOne c.2 W) =
    (originalScheduledPrimeCharacter bound i.val g
      (Multiplicative.ofAdd (originalChartIntegerShift c (originalScheduledChartBlockDegree bound k i))) : ℂ) *
      originalPositiveTorusEvaluation Z W (originalScheduledChartCharacterBlockPolynomial c bound k i
        (originalScheduledChartPrimeTorus c bound i.val g)) := by
  have h : originalScheduledBlockHomogeneousPolynomial bound k i (originalChartHomogeneousZero c.1 Z)
      ((g.1.val : ℂ) * originalChartHomogeneousOne c.1 Z) (originalChartHomogeneousZero c.2 W)
      ((g.2.val : ℂ) * originalChartHomogeneousOne c.2 W) =
      originalPositiveTorusEvaluation Z W (originalPositiveChartReflection c (originalScheduledChartBlockDegree bound k i)
        (originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
          (originalScheduledBlockPositivePolynomial bound k i))) := by
    rw [originalScheduledBlock_chart_character_product, map_prod]
    unfold originalScheduledBlockHomogeneousPolynomial
    exact Finset.prod_congr rfl (fun j _ => originalPositiveSheetHomogeneous_chart_character_eval c _ _ _ _ Z W)
  rw [h, originalPositiveChartReflection_twist c _ _ _
    (originalScheduledBlockPositivePolynomial_inSquare bound k i),
    originalScheduledChartPrimeCharacter, map_smul]
  change _ * originalPositiveTorusEvaluation Z W
    (originalPositiveCharacterTwist _ (originalScheduledChartBlockPolynomial c bound k i)) = _
  rw [originalScheduledChartBlock_character_twist]

/-- EVERY actual original divisor orbit has no common zero on ANY fixed native chart,
including its axes, infinity boundaries and corners. All orbit inputs are internal. -/
theorem originalScheduledChartBlock_full_orbit_avoids (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (Z W : ℂ) :
    ∃ g : OriginalScheduledPrimeTorus bound i.val,
      originalPositiveTorusEvaluation Z W (originalScheduledChartCharacterBlockPolynomial c bound k i g) ≠ 0 := by
  obtain ⟨g, hg⟩ := originalScheduledBlock_full_divisor_orbit_avoids bound k i
    (originalChartHomogeneousZero c.1 Z) (originalChartHomogeneousOne c.1 Z)
    (originalChartHomogeneousZero c.2 W) (originalChartHomogeneousOne c.2 W)
    (originalChartHomogeneous_nonzero c.1 Z) (originalChartHomogeneous_nonzero c.2 W)
  rw [originalScheduledBlockHomogeneousPolynomial_chart_character_eval c bound k i g Z W] at hg
  exact ⟨originalScheduledChartPrimeTorus c bound i.val g, (mul_ne_zero_iff.mp hg).2⟩

end
end MeyerGeneralProblem.StrongParity
