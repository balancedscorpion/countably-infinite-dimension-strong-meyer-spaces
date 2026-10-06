module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalSheetPrimes

@[expose] public section

/-! Complete actual block factor products and their structural relative primality.
All factors and character substitutions are literal original coefficients.
Common zeros at crossings remain possible and are not excluded by relative primality. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The whole actual original block after any character in its private prime torus. -/
def originalScheduledCharacterBlockPolynomial (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  ∏ j : Fin (originalReflectedOrderSchedule bound i.val),
    originalScheduledCharacterSheetPolynomial bound k i j g

/-- The identity character recovers the exact original whole block, with every sheet retained. -/
theorem originalScheduledCharacterBlockPolynomial_one (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    originalScheduledCharacterBlockPolynomial bound k i (originalScheduledPrimeTorusIdentity bound i.val) =
      originalScheduledBlockPositivePolynomial bound k i := by
  simp only [originalScheduledCharacterBlockPolynomial, originalScheduledBlockPositivePolynomial,
    originalScheduledCharacterSheetPolynomial_one]

/-- The actual character block evaluates to the exact full translated original block. -/
theorem originalScheduledCharacterBlockPolynomial_eval (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) (Z W : ℂ) :
    originalPositiveTorusEvaluation Z W (originalScheduledCharacterBlockPolynomial bound k i g) =
      originalPositiveTorusEvaluation ((g.1.val : ℂ) * Z) ((g.2.val : ℂ) * W)
        (originalScheduledBlockPositivePolynomial bound k i) := by
  simp only [originalScheduledCharacterBlockPolynomial, originalScheduledBlockPositivePolynomial,
    map_prod, originalScheduledCharacterSheetPolynomial_eval]

/-- Every whole actual character block is nonzero, supplied by all its actual prime factors. -/
theorem originalScheduledCharacterBlockPolynomial_ne_zero (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledCharacterBlockPolynomial bound k i g ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact (originalScheduledCharacterSheetPolynomial_prime bound k i j g).ne_zero

/-- Every prime divisor of an actual full character block is exactly one actual sheet factor. -/
theorem originalScheduledCharacterBlockPolynomial_prime_dvd_iff (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (g : OriginalScheduledPrimeTorus bound i.val)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : Prime p) :
    p ∣ originalScheduledCharacterBlockPolynomial bound k i g ↔
      ∃ j : Fin (originalReflectedOrderSchedule bound i.val),
        Associated p (originalScheduledCharacterSheetPolynomial bound k i j g) := by
  rw [originalScheduledCharacterBlockPolynomial, hp.dvd_finset_prod_iff]
  constructor
  · rintro ⟨j, _, hj⟩
    exact ⟨j, hp.irreducible.associated_of_dvd
      (originalScheduledCharacterSheetPolynomial_prime bound k i j g).irreducible hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, Finset.mem_univ j, hj.dvd⟩

/-- EVERY pair of distinct actual block products has no common nonunit factor,
including arbitrary actual character translates. No coprimality certificate is supplied. -/
theorem originalScheduledCharacterBlocks_other_block_isRelPrime
    (bound : ℕ → ℕ) (k : ℕ) (i t : Fin k) (hit : i ≠ t)
    (g : OriginalScheduledPrimeTorus bound i.val) (h : OriginalScheduledPrimeTorus bound t.val) :
    IsRelPrime (originalScheduledCharacterBlockPolynomial bound k i g)
      (originalScheduledCharacterBlockPolynomial bound k t h) := by
  apply IsRelPrime.prod_left
  intro j _
  apply IsRelPrime.prod_right
  intro l _
  exact originalScheduledCharacterSheetPolynomial_other_block_isRelPrime bound k i t hit j l g h

/-- Different actual characters of one full block give no common nonunit factor. -/
theorem originalScheduledCharacterBlocks_same_block_isRelPrime
    (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g h : OriginalScheduledPrimeTorus bound i.val) (hgh : g ≠ h) :
    IsRelPrime (originalScheduledCharacterBlockPolynomial bound k i g)
      (originalScheduledCharacterBlockPolynomial bound k i h) := by
  apply IsRelPrime.prod_left
  intro j _
  apply IsRelPrime.prod_right
  intro l _
  exact originalScheduledCharacterSheetPolynomial_same_block_isRelPrime bound k i j l g h
    (Or.inr hgh)

/-- The two whole original blocks have no common nonunit factor, with their literal quarter phase. -/
theorem originalScheduledBlockPositivePolynomial_other_isRelPrime
    (bound : ℕ → ℕ) (k : ℕ) (i t : Fin k) (hit : i ≠ t) :
    IsRelPrime (originalScheduledBlockPositivePolynomial bound k i)
      (originalScheduledBlockPositivePolynomial bound k t) := by
  rw [← originalScheduledCharacterBlockPolynomial_one,
    ← originalScheduledCharacterBlockPolynomial_one]
  exact originalScheduledCharacterBlocks_other_block_isRelPrime bound k i t hit _ _

end
end MeyerGeneralProblem.StrongParity
