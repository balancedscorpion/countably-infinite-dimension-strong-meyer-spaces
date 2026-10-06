module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalSheetChartNormalization

@[expose] public section

/-! Actual native sheet prime factors on ALL four projective charts. Literal
quarter phases remain after native powers, reciprocal parameters are justified
internally, and relative primality allows divisor crossings. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual original quarter phase, inverted ONLY on a reversed second coordinate. -/
def originalScheduledChartQuarterPhase (c : Bool × Bool) : ℂ :=
  originalSheetChartSecondPhase c (complexUnitPhase (-1 / 4))

/-- The literal normalized phased sheet on its actual native projective chart. -/
def originalScheduledChartSheetNormalized (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (j : Fin (originalReflectedOrderSchedule bound i.val)) (g : OriginalScheduledPrimeTorus bound i.val) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  originalPhasedPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
    (originalSheetChartParameter c ((originalScheduledParameterBlock bound i.val).parameter j))
    ((g.1.val : ℂ) ^ originalScheduledPrefixCoordinateDilation bound k i)
    (originalScheduledChartQuarterPhase c * (g.2.val : ℂ) ^ originalScheduledPrefixCoordinateDilation bound k i)

/-- The exact scalar of the ACTUAL original sheet chart, independent of the acting character. -/
def originalScheduledChartSheetScalar (c : Bool × Bool) (bound : ℕ → ℕ) (i : ℕ)
    (j : Fin (originalReflectedOrderSchedule bound i)) : ℂ :=
  originalSheetChartScalar c ((originalScheduledParameterBlock bound i).parameter j) 1 (complexUnitPhase (-1 / 4))

/-- Actual native character action on the WHOLE reflected original sheet. -/
def originalScheduledChartSheetPolynomial (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (j : Fin (originalReflectedOrderSchedule bound i.val)) (g : OriginalScheduledPrimeTorus bound i.val) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
    (originalPositiveChartReflection c (originalScheduledPrefixCoordinateDilation bound k i)
      (originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
        ((originalScheduledParameterBlock bound i.val).parameter j)))

/-- The original quarter phase stays nonzero on EVERY projective chart. -/
theorem originalScheduledChartQuarterPhase_ne_zero (c : Bool × Bool) : originalScheduledChartQuarterPhase c ≠ 0 :=
  (originalSheetChartPhases_ne_zero c 1 _ one_ne_zero originalQuarterPhase_ne_zero).2

/-- EVERY actual original sheet chart scalar is a genuine complex polynomial unit. -/
theorem originalScheduledChartSheetScalar_isUnit (c : Bool × Bool) (bound : ℕ → ℕ) (i : ℕ)
    (j : Fin (originalReflectedOrderSchedule bound i)) :
    IsUnit (algebraMap ℂ (AddMonoidAlgebra ℂ (ℕ × ℕ)) (originalScheduledChartSheetScalar c bound i j)) :=
  originalPositivePolynomial_constant_isUnit _
    (originalSheetChartScalar_ne_zero c _ 1 _
      ((originalScheduledParameterBlock bound i).parameter_bounds j).1.ne' one_ne_zero originalQuarterPhase_ne_zero)

/-- EVERY actual native sheet on EVERY chart equals its literal unit times the correctly phased normalized sheet. -/
theorem originalScheduledChartSheetPolynomial_normalization (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (j : Fin (originalReflectedOrderSchedule bound i.val))
    (g : OriginalScheduledPrimeTorus bound i.val) :
    originalScheduledChartSheetPolynomial c bound k i j g =
      originalScheduledChartSheetScalar c bound i.val j • originalScheduledChartSheetNormalized c bound k i j g := by
  unfold originalScheduledChartSheetPolynomial
  rw [← originalPhasedPositiveSheetPolynomial_original,
    originalPhasedPositiveSheetPolynomial_chart_normalization c _ _ 1 _
      ((originalScheduledParameterBlock bound i.val).parameter_bounds j).1.ne' one_ne_zero originalQuarterPhase_ne_zero,
    map_smul]
  unfold originalScheduledPrimeCharacter
  rw [originalPositiveCharacterTwist_phased_sheet]
  have hf : originalSheetChartFirstPhase c 1 = 1 := by simp [originalSheetChartFirstPhase]
  rw [hf, one_mul]
  rfl

/-- EVERY actual native sheet/character chart is prime, with ALL reciprocal and phase inputs internal. -/
theorem originalScheduledChartSheetPolynomial_prime (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (j : Fin (originalReflectedOrderSchedule bound i.val))
    (g : OriginalScheduledPrimeTorus bound i.val) : Prime (originalScheduledChartSheetPolynomial c bound k i j g) := by
  have ha := originalSheetChartParameter_nondegenerate c _ ((originalScheduledParameterBlock bound i.val).parameter_bounds j)
  have hp : Prime (originalScheduledChartSheetNormalized c bound k i j g) := by
    apply originalPhasedPositiveSheetPolynomial_prime_of_nondegenerate _
      (originalScheduledPrefixCoordinateDilation_pos bound k i) _ ha.2.1 ha.2.2
    · exact pow_ne_zero _ (Units.ne_zero g.1.val)
    · exact mul_ne_zero (originalScheduledChartQuarterPhase_ne_zero c) (pow_ne_zero _ (Units.ne_zero g.2.val))
  rw [originalScheduledChartSheetPolynomial_normalization, Algebra.smul_def]
  exact (associated_unit_mul_right _ _ (originalScheduledChartSheetScalar_isUnit c bound i.val j)).prime hp

/-- Nonzero actual normalization units can be removed from associate comparisons internally. -/
theorem originalScheduledChartSheets_associated_normalized_iff (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i t : Fin k) (j : Fin (originalReflectedOrderSchedule bound i.val))
    (l : Fin (originalReflectedOrderSchedule bound t.val))
    (g : OriginalScheduledPrimeTorus bound i.val) (h : OriginalScheduledPrimeTorus bound t.val) :
    Associated (originalScheduledChartSheetPolynomial c bound k i j g)
      (originalScheduledChartSheetPolynomial c bound k t l h) ↔
    Associated (originalScheduledChartSheetNormalized c bound k i j g)
      (originalScheduledChartSheetNormalized c bound k t l h) := by
  rw [originalScheduledChartSheetPolynomial_normalization, originalScheduledChartSheetPolynomial_normalization,
    Algebra.smul_def, Algebra.smul_def,
    associated_isUnit_mul_left_iff (originalScheduledChartSheetScalar_isUnit c bound i.val j),
    associated_isUnit_mul_right_iff (originalScheduledChartSheetScalar_isUnit c bound t.val l)]

/-- Within an actual whole block, chart associates identify the sheet AND full native character exactly. -/
theorem originalScheduledChartSheetPolynomial_associated_iff (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (j l : Fin (originalReflectedOrderSchedule bound i.val))
    (g h : OriginalScheduledPrimeTorus bound i.val) :
    Associated (originalScheduledChartSheetPolynomial c bound k i j g)
      (originalScheduledChartSheetPolynomial c bound k i l h) ↔ j = l ∧ g = h := by
  have haj := originalSheetChartParameter_nondegenerate c _ ((originalScheduledParameterBlock bound i.val).parameter_bounds j)
  have hal := originalSheetChartParameter_nondegenerate c _ ((originalScheduledParameterBlock bound i.val).parameter_bounds l)
  have hg := originalScheduledNativeCharacterPhases_norm bound k i g
  have hh := originalScheduledNativeCharacterPhases_norm bound k i h
  rw [originalScheduledChartSheets_associated_normalized_iff]
  simp only [originalScheduledChartSheetNormalized]
  rw [originalPhasedPositiveSheetPolynomial_associated_iff _ _
    (originalScheduledPrefixCoordinateDilation_pos bound k i)
    (originalScheduledPrefixCoordinateDilation_pos bound k i) _ _ haj.1 hal.1 _ _ _ _ hg.1 hh.1]
  constructor
  · rintro ⟨_, hparam, hfirst, hsecond⟩
    have hcop := originalScheduledPrefixCoordinateDilation_coprime bound k i
    have h1 := originalRootOfUnity_native_power_injective _ _ hcop hfirst
    have h2 := originalRootOfUnity_native_power_injective _ _ hcop
      (mul_left_cancel₀ (originalScheduledChartQuarterPhase_ne_zero c) hsecond)
    exact ⟨(originalScheduledParameterBlock bound i.val).injective
      (originalSheetChartParameter_injective c hparam), Prod.ext h1 h2⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- EVERY pair of sheets in distinct actual blocks has no common nonunit factor on ANY chart. -/
theorem originalScheduledChartSheetPolynomial_other_block_isRelPrime (c : Bool × Bool)
    (bound : ℕ → ℕ) (k : ℕ) (i t : Fin k) (hit : i ≠ t)
    (j : Fin (originalReflectedOrderSchedule bound i.val)) (l : Fin (originalReflectedOrderSchedule bound t.val))
    (g : OriginalScheduledPrimeTorus bound i.val) (h : OriginalScheduledPrimeTorus bound t.val) :
    IsRelPrime (originalScheduledChartSheetPolynomial c bound k i j g)
      (originalScheduledChartSheetPolynomial c bound k t l h) := by
  have hp := (originalScheduledChartSheetPolynomial_prime c bound k i j g).irreducible
  have hq := (originalScheduledChartSheetPolynomial_prime c bound k t l h).irreducible
  apply hp.isRelPrime_iff_not_dvd.mpr
  intro hdvd
  have ha := (originalScheduledChartSheets_associated_normalized_iff c bound k i t j l g h).mp
    (hp.associated_of_dvd hq hdvd)
  have he := originalPositivePolynomial_associated_eq_of_normalized _ _
    (originalPhasedPositiveSheetPolynomial_origin _ (originalScheduledPrefixCoordinateDilation_pos bound k i) _ _ _)
    (originalPhasedPositiveSheetPolynomial_origin _ (originalScheduledPrefixCoordinateDilation_pos bound k t) _ _ _) ha
  have hde := originalPhasedPositiveSheetPolynomial_eq_dilation _ _
    (originalScheduledPrefixCoordinateDilation_pos bound k i)
    (originalScheduledPrefixCoordinateDilation_pos bound k t) _ _
    (originalSheetChartParameter_nondegenerate c _ ((originalScheduledParameterBlock bound i.val).parameter_bounds j)).1 _ _ _ _
    (pow_ne_zero _ (Units.ne_zero g.1.val)) he
  exact hit (originalScheduledPrefixCoordinateDilation_injective bound k hde)

/-- Distinct actual sheet/character labels on the same chart have no common nonunit factor. -/
theorem originalScheduledChartSheetPolynomial_same_block_isRelPrime (c : Bool × Bool)
    (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) (j l : Fin (originalReflectedOrderSchedule bound i.val))
    (g h : OriginalScheduledPrimeTorus bound i.val) (hne : j ≠ l ∨ g ≠ h) :
    IsRelPrime (originalScheduledChartSheetPolynomial c bound k i j g)
      (originalScheduledChartSheetPolynomial c bound k i l h) := by
  have hp := (originalScheduledChartSheetPolynomial_prime c bound k i j g).irreducible
  have hq := (originalScheduledChartSheetPolynomial_prime c bound k i l h).irreducible
  apply hp.isRelPrime_iff_not_dvd.mpr
  intro hdvd
  have he := (originalScheduledChartSheetPolynomial_associated_iff c bound k i j l g h).mp
    (hp.associated_of_dvd hq hdvd)
  exact hne.elim (fun hn => hn he.1) (fun hn => hn he.2)

/-- EVERY other actual private prime fixes ALL full native chart sheet translates internally. -/
theorem originalScheduledChartSheetPolynomial_other_character_invariant (c : Bool × Bool)
    (bound : ℕ → ℕ) (k : ℕ) (i t : Fin k) (hit : i ≠ t)
    (j : Fin (originalReflectedOrderSchedule bound t.val))
    (g : OriginalScheduledPrimeTorus bound i.val) (h : OriginalScheduledPrimeTorus bound t.val) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i.val g)
      (originalScheduledChartSheetPolynomial c bound k t j h) = originalScheduledChartSheetPolynomial c bound k t j h := by
  rw [originalScheduledChartSheetPolynomial_normalization, map_smul]
  unfold originalScheduledChartSheetNormalized originalScheduledPrimeCharacter
  rw [originalPositiveCharacterTwist_phased_sheet,
    originalScheduledPrimeRoot_other_native_power bound k i t hit g.1,
    originalScheduledPrimeRoot_other_native_power bound k i t hit g.2, mul_one, mul_one]

/-- The actual identity torus acts trivially on EVERY positive polynomial. -/
theorem originalScheduledPositiveCharacter_identity (bound : ℕ → ℕ) (i : ℕ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound i (originalScheduledPrimeTorusIdentity bound i)) p = p := by
  ext n
  rw [originalPositiveCharacterTwist_coefficient]
  simp [originalScheduledPrimeCharacter, originalScheduledPrimeTorusIdentity, originalIntegerTorusCharacter]

/-- The identity character chart sheet is EXACTLY the reflected actual original sheet. -/
theorem originalScheduledChartSheetPolynomial_identity (c : Bool × Bool) (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (j : Fin (originalReflectedOrderSchedule bound i.val)) :
    originalScheduledChartSheetPolynomial c bound k i j (originalScheduledPrimeTorusIdentity bound i.val) =
      originalPositiveChartReflection c (originalScheduledPrefixCoordinateDilation bound k i)
        (originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
          ((originalScheduledParameterBlock bound i.val).parameter j)) :=
  originalScheduledPositiveCharacter_identity bound i.val _

end
end MeyerGeneralProblem.StrongParity
