module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalChartSheetFactors
public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalChartNumerators

@[expose] public section

/-! Exact whole-block products on ALL four fixed native charts. Product degrees,
nonzero denominators and relative primality follow from the actual sheet factors.
No assertion excludes crossings of relatively prime divisors. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The full square degree of one actual block, including every original sheet. -/
def originalScheduledChartBlockDegree (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) : ℕ :=
  originalReflectedOrderSchedule bound i.val * originalScheduledPrefixCoordinateDilation bound k i

/-- The entire original block reflected at its OWN full block degree. -/
def originalScheduledChartBlockPolynomial (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  originalPositiveChartReflection c (originalScheduledChartBlockDegree bound k i)
    (originalScheduledBlockPositivePolynomial bound k i)

/-- ALL actual reflected sheet translates, with the literal chart quarter phase. -/
def originalScheduledChartCharacterBlockPolynomial (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  ∏ j : Fin (originalReflectedOrderSchedule bound i.val), originalScheduledChartSheetPolynomial c bound k i j g

/-- The exact entire other-block product on its fixed chart. -/
def originalScheduledChartOtherBlocksPolynomial (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  ∏ j ∈ Finset.univ.erase i, originalScheduledChartBlockPolynomial c bound k j

/-- Every actual whole block has its internally computed native square. -/
theorem originalScheduledBlockPositivePolynomial_inSquare (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    OriginalPositiveInSquare (originalScheduledBlockPositivePolynomial bound k i)
      (originalScheduledChartBlockDegree bound k i) := by
  have h := originalPositiveInSquare_prod Finset.univ
    (fun j : Fin (originalReflectedOrderSchedule bound i.val) =>
      originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
        ((originalScheduledParameterBlock bound i.val).parameter j))
    (fun _ => originalScheduledPrefixCoordinateDilation bound k i)
    (fun j _ => by
      rw [← originalPhasedPositiveSheetPolynomial_original]
      exact originalPhasedPositiveSheetPolynomial_inSquare _ _ _ _)
  simpa [originalScheduledBlockPositivePolynomial, originalScheduledChartBlockDegree] using h

/-- The identity chart product is exactly the fixed-degree reflection of the whole block. -/
theorem originalScheduledChartCharacterBlockPolynomial_one (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    originalScheduledChartCharacterBlockPolynomial c bound k i (originalScheduledPrimeTorusIdentity bound i.val) =
      originalScheduledChartBlockPolynomial c bound k i := by
  have h := originalPositiveChartReflection_prod c Finset.univ
    (fun j : Fin (originalReflectedOrderSchedule bound i.val) =>
      originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
        ((originalScheduledParameterBlock bound i.val).parameter j))
    (fun _ => originalScheduledPrefixCoordinateDilation bound k i)
    (fun j _ => by
      rw [← originalPhasedPositiveSheetPolynomial_original]
      exact originalPhasedPositiveSheetPolynomial_inSquare _ _ _ _)
  simpa [originalScheduledChartCharacterBlockPolynomial, originalScheduledChartBlockPolynomial,
    originalScheduledChartBlockDegree, originalScheduledBlockPositivePolynomial,
    originalScheduledChartSheetPolynomial_identity] using h.symm

/-- Genuine character action gives the ENTIRE actual chart block product. -/
theorem originalScheduledChartBlock_character_twist (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledChartBlockPolynomial c bound k i) =
      originalScheduledChartCharacterBlockPolynomial c bound k i g := by
  rw [← originalScheduledChartCharacterBlockPolynomial_one]
  simp only [originalScheduledChartCharacterBlockPolynomial, map_prod,
    originalScheduledChartSheetPolynomial_identity]
  rfl

/-- Every chart character block is nonzero, internally from EVERY actual sheet prime. -/
theorem originalScheduledChartCharacterBlockPolynomial_ne_zero (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledChartCharacterBlockPolynomial c bound k i g ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact (originalScheduledChartSheetPolynomial_prime c bound k i j g).ne_zero

/-- Every pair of distinct actual chart block translates has no common nonunit factor. -/
theorem originalScheduledChartCharacterBlocks_other_block_isRelPrime (c : Bool × Bool)
    (bound : ℕ → ℕ) (k : ℕ) (i t : Fin k) (hit : i ≠ t)
    (g : OriginalScheduledPrimeTorus bound i.val) (h : OriginalScheduledPrimeTorus bound t.val) :
    IsRelPrime (originalScheduledChartCharacterBlockPolynomial c bound k i g)
      (originalScheduledChartCharacterBlockPolynomial c bound k t h) := by
  apply IsRelPrime.prod_left
  intro j _
  apply IsRelPrime.prod_right
  intro l _
  exact originalScheduledChartSheetPolynomial_other_block_isRelPrime c bound k i t hit j l g h

/-- Different full actual characters of one chart block have no common nonunit factor. -/
theorem originalScheduledChartCharacterBlocks_same_block_isRelPrime (c : Bool × Bool)
    (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g h : OriginalScheduledPrimeTorus bound i.val) (hgh : g ≠ h) :
    IsRelPrime (originalScheduledChartCharacterBlockPolynomial c bound k i g)
      (originalScheduledChartCharacterBlockPolynomial c bound k i h) := by
  apply IsRelPrime.prod_left
  intro j _
  apply IsRelPrime.prod_right
  intro l _
  exact originalScheduledChartSheetPolynomial_same_block_isRelPrime c bound k i j l g h (Or.inr hgh)

/-- Actual distinct WHOLE chart blocks remain relatively prime on EVERY chart. -/
theorem originalScheduledChartBlockPolynomial_other_isRelPrime (c : Bool × Bool)
    (bound : ℕ → ℕ) (k : ℕ) (i t : Fin k) (hit : i ≠ t) :
    IsRelPrime (originalScheduledChartBlockPolynomial c bound k i)
      (originalScheduledChartBlockPolynomial c bound k t) := by
  rw [← originalScheduledChartCharacterBlockPolynomial_one, ← originalScheduledChartCharacterBlockPolynomial_one]
  exact originalScheduledChartCharacterBlocks_other_block_isRelPrime c bound k i t hit _ _

/-- Every other actual private prime fixes the WHOLE native chart translate. -/
theorem originalScheduledChartCharacterBlock_other_invariant (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledChartCharacterBlockPolynomial c bound k j h) =
      originalScheduledChartCharacterBlockPolynomial c bound k j h := by
  unfold originalScheduledChartCharacterBlockPolynomial
  rw [map_prod]
  exact Finset.prod_congr rfl (fun l _ => originalScheduledChartSheetPolynomial_other_character_invariant c bound k i j hij l g h)

/-- The other actual prime fixes the identity whole chart block internally. -/
theorem originalScheduledChartBlock_other_character_invariant (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledChartBlockPolynomial c bound k j) = originalScheduledChartBlockPolynomial c bound k j := by
  rw [← originalScheduledChartCharacterBlockPolynomial_one]
  exact originalScheduledChartCharacterBlock_other_invariant c bound k i j hij g _

/-- The complete chart denominator factors into ALL whole blocks at their exact full degrees. -/
theorem originalScheduledPrefixChartPolynomial_eq_block_product (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) :
    originalScheduledPrefixChartPolynomial c bound k = ∏ i : Fin k, originalScheduledChartBlockPolynomial c bound k i := by
  unfold originalScheduledPrefixChartPolynomial
  rw [originalScheduledPrefixPolynomial_eq_block_product]
  exact originalPositiveChartReflection_prod c Finset.univ _ _
    (fun i _ => originalScheduledBlockPositivePolynomial_inSquare bound k i)

/-- The actual WHOLE chart denominator is the selected block times its exact complement. -/
theorem originalScheduledPrefixChartPolynomial_block_complement (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    originalScheduledPrefixChartPolynomial c bound k = originalScheduledChartBlockPolynomial c bound k i *
      originalScheduledChartOtherBlocksPolynomial c bound k i := by
  classical
  rw [originalScheduledPrefixChartPolynomial_eq_block_product]
  exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm

/-- The selected actual prime fixes its ENTIRE chart complement. -/
theorem originalScheduledChartOtherBlocksPolynomial_character_invariant (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledChartOtherBlocksPolynomial c bound k i) = originalScheduledChartOtherBlocksPolynomial c bound k i := by
  classical
  unfold originalScheduledChartOtherBlocksPolynomial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  exact originalScheduledChartBlock_other_character_invariant c bound k i j (Finset.mem_erase.mp hj).1.symm g

/-- The genuine chart denominator twists to ONE translated block and its unchanged complement. -/
theorem originalScheduledPrefixChartPolynomial_character_factorization (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledPrefixChartPolynomial c bound k) =
      originalScheduledChartCharacterBlockPolynomial c bound k i g * originalScheduledChartOtherBlocksPolynomial c bound k i := by
  rw [originalScheduledPrefixChartPolynomial_block_complement c bound k i, map_mul,
    originalScheduledChartBlock_character_twist, originalScheduledChartOtherBlocksPolynomial_character_invariant]

/-- ALL actual chart complement factors are nonzero, including the empty complement. -/
theorem originalScheduledChartOtherBlocksPolynomial_ne_zero (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    originalScheduledChartOtherBlocksPolynomial c bound k i ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [← originalScheduledChartCharacterBlockPolynomial_one]
  exact originalScheduledChartCharacterBlockPolynomial_ne_zero c bound k j _

end
end MeyerGeneralProblem.StrongParity
