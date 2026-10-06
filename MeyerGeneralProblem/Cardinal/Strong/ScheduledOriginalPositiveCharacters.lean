module

public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalCharacterTwists
public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalBlockFactors
public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalDivisorCharacters

@[expose] public section

/-! The actual positive character action gives the same native original sheet and
whole-block factors used by the prime classification. Every other whole block is
fixed internally. The complete denominator factors into one translated block and
its unchanged literal complement, with all native phases retained. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- A genuine native character changes both phased sheet coefficients by the exact native powers. -/
theorem originalPositiveCharacterTwist_phased_sheet (ζ η : ℂˣ) (d : ℕ) (a : ℝ) (ρ σ : ℂ) :
    originalPositiveCharacterTwist (originalIntegerTorusCharacter ζ η)
      (originalPhasedPositiveSheetPolynomial d a ρ σ) =
      originalPhasedPositiveSheetPolynomial d a (ρ * (ζ : ℂ) ^ d) (σ * (η : ℂ) ^ d) := by
  have hc (n : ℕ × ℕ) :
      (originalIntegerTorusCharacter ζ η (Multiplicative.ofAdd (originalNativeIntegerEmbedding n)) : ℂ) =
      (ζ : ℂ) ^ n.1 * (η : ℂ) ^ n.2 := by
    change ((ζ ^ (n.1 : ℤ) * η ^ (n.2 : ℤ) : ℂˣ) : ℂ) = _
    simp only [Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
  simp [originalPhasedPositiveSheetPolynomial, originalPositiveCharacterTwist_single,
    hc, mul_assoc, mul_left_comm, mul_comm]

/-- The genuine positive action is exactly the actual original translated sheet, retaining its quarter phase. -/
theorem originalScheduledPositiveSheet_character_twist (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (j : Fin (originalReflectedOrderSchedule bound i.val)) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
        ((originalScheduledParameterBlock bound i.val).parameter j)) =
      originalScheduledCharacterSheetPolynomial bound k i j g := by
  rw [← originalPhasedPositiveSheetPolynomial_original]
  unfold originalScheduledPrimeCharacter
  rw [originalPositiveCharacterTwist_phased_sheet]
  simp only [originalScheduledCharacterSheetPolynomial, one_mul]

/-- Every actual full native block twists to its exact original whole character block. -/
theorem originalScheduledPositiveBlock_character_twist (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledBlockPositivePolynomial bound k i) =
      originalScheduledCharacterBlockPolynomial bound k i g := by
  simp only [originalScheduledBlockPositivePolynomial, map_prod,
    originalScheduledPositiveSheet_character_twist, originalScheduledCharacterBlockPolynomial]

/-- Each actual prime character fixes every other complete original positive block polynomial. -/
theorem originalScheduledPositiveBlock_other_character_invariant (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledBlockPositivePolynomial bound k j) = originalScheduledBlockPositivePolynomial bound k j := by
  unfold originalScheduledBlockPositivePolynomial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro l _
  rw [← originalPhasedPositiveSheetPolynomial_original]
  unfold originalScheduledPrimeCharacter
  rw [originalPositiveCharacterTwist_phased_sheet,
    originalScheduledPrimeRoot_other_native_power bound k i j hij g.1,
    originalScheduledPrimeRoot_other_native_power bound k i j hij g.2, mul_one, mul_one]

/-- Other actual prime actions also fix EVERY whole character translate of a block. -/
theorem originalScheduledPositiveCharacterBlock_other_invariant (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledCharacterBlockPolynomial bound k j h) =
      originalScheduledCharacterBlockPolynomial bound k j h := by
  rw [← originalScheduledPositiveBlock_character_twist, ← originalPositiveCharacterTwist_mul,
    mul_comm (originalScheduledPrimeCharacter bound i.val g), originalPositiveCharacterTwist_mul,
    originalScheduledPositiveBlock_other_character_invariant bound k i j hij g]

/-- The literal complement consists of ALL other actual original whole block factors. -/
def originalScheduledOtherBlocksPolynomial (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  ∏ j ∈ Finset.univ.erase i, originalScheduledBlockPositivePolynomial bound k j

/-- The genuine complete original denominator is its selected whole block times the exact complement. -/
theorem originalScheduledPrefixPolynomial_block_complement (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    originalScheduledPrefixPolynomial bound k = originalScheduledBlockPositivePolynomial bound k i *
      originalScheduledOtherBlocksPolynomial bound k i := by
  classical
  rw [originalScheduledPrefixPolynomial_eq_block_product]
  exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm

/-- The actual selected prime action leaves the complete original complement unchanged. -/
theorem originalScheduledOtherBlocksPolynomial_character_invariant (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledOtherBlocksPolynomial bound k i) = originalScheduledOtherBlocksPolynomial bound k i := by
  classical
  unfold originalScheduledOtherBlocksPolynomial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  exact originalScheduledPositiveBlock_other_character_invariant bound k i j
    (Finset.mem_erase.mp hj).1.symm g

/-- The complete actual mixed denominator twists to precisely one translated whole block,
times the exact unchanged complement. No factorization certificate is supplied. -/
theorem originalScheduledPrefixPolynomial_character_factorization (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledPrefixPolynomial bound k) =
      originalScheduledCharacterBlockPolynomial bound k i g * originalScheduledOtherBlocksPolynomial bound k i := by
  rw [originalScheduledPrefixPolynomial_block_complement bound k i, map_mul,
    originalScheduledPositiveBlock_character_twist, originalScheduledOtherBlocksPolynomial_character_invariant]

/-- ALL actual other-block factors give a nonzero literal complement, including an empty complement. -/
theorem originalScheduledOtherBlocksPolynomial_ne_zero (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    originalScheduledOtherBlocksPolynomial bound k i ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [← originalScheduledCharacterBlockPolynomial_one]
  exact originalScheduledCharacterBlockPolynomial_ne_zero bound k j _

/-- Every actual translate of the selected whole block is relatively prime to its genuine complement. -/
theorem originalScheduledCharacterBlock_complement_isRelPrime (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    IsRelPrime (originalScheduledCharacterBlockPolynomial bound k i g)
      (originalScheduledOtherBlocksPolynomial bound k i) := by
  classical
  apply IsRelPrime.prod_right
  intro j hj
  rw [← originalScheduledCharacterBlockPolynomial_one]
  exact originalScheduledCharacterBlocks_other_block_isRelPrime bound k i j
    (Finset.mem_erase.mp hj).1.symm g _

end
end MeyerGeneralProblem.StrongParity
