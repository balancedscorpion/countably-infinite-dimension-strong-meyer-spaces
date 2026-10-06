module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalSheetAssociates
public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalDivisorOrbit

@[expose] public section

/-! Actual scheduled sheets and ALL private-prime translates are prime.
Their genuine native dilations, real parameters, root phases and associate
classification are supplied by the original construction itself. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual distinct private primes give distinct common-coordinate native dilations. -/
theorem originalScheduledPrefixCoordinateDilation_injective (bound : ℕ → ℕ) (k : ℕ) :
    Function.Injective (originalScheduledPrefixCoordinateDilation bound k) := by
  intro i j hij
  have he : originalReflectedPrimeSchedule bound i.val = originalReflectedPrimeSchedule bound j.val := by
    apply Nat.eq_of_mul_eq_mul_left (originalScheduledPrefixCoordinateDilation_pos bound k i)
    rw [originalScheduledPrefixCoordinateDilation_mul_prime, hij,
      originalScheduledPrefixCoordinateDilation_mul_prime]
  apply Fin.ext
  exact originalPrivatePrimeSchedule_injective (originalReflectedWindowBounds bound) he

/-- Raising members of a root group to a coprime native power is injective. -/
theorem originalRootOfUnity_native_power_injective (m d : ℕ) (hdm : d.Coprime m) :
    Function.Injective (fun ζ : rootsOfUnity m ℂ => (ζ.val : ℂ) ^ d) := by
  intro ζ η he
  have hu : ζ.val ^ d = η.val ^ d := Units.ext he
  have hd : (ζ.val * η.val⁻¹) ^ d = 1 := by
    rw [mul_pow, inv_pow, hu, mul_inv_cancel]
  have hm : (ζ.val * η.val⁻¹) ^ m = 1 := by
    rw [mul_pow, inv_pow, (mem_rootsOfUnity m ζ.val).mp ζ.property,
      (mem_rootsOfUnity m η.val).mp η.property, inv_one, mul_one]
  have ho := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hd) (orderOf_dvd_of_pow_eq_one hm)
  rw [hdm.gcd_eq_one] at ho
  have h1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one ho)
  apply Subtype.ext
  exact mul_inv_eq_one.mp h1

/-- Every ACTUAL scheduled prime root has complex norm one. -/
theorem originalScheduledPrimeRoot_norm (bound : ℕ → ℕ) (i : ℕ)
    (ζ : rootsOfUnity (originalReflectedPrimeSchedule bound i) ℂ) : ‖(ζ.val : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one _ (originalScheduledBlockPrime_pos bound i).ne'
  have hm : ζ.val ^ originalReflectedPrimeSchedule bound i = 1 :=
    (mem_rootsOfUnity _ ζ.val).mp ζ.property
  have hc := congrArg (fun u : ℂˣ => (u : ℂ)) hm
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hc

/-- Both actual native character phases have norm one, with the original quarter phase outside the power. -/
theorem originalScheduledNativeCharacterPhases_norm (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (g : OriginalScheduledPrimeTorus bound i.val) :
    ‖(g.1.val : ℂ) ^ originalScheduledPrefixCoordinateDilation bound k i‖ = 1 ∧
    ‖complexUnitPhase (-1 / 4) * (g.2.val : ℂ) ^ originalScheduledPrefixCoordinateDilation bound k i‖ = 1 := by
  constructor
  · rw [norm_pow, originalScheduledPrimeRoot_norm, one_pow]
  · rw [norm_mul, norm_pow, originalScheduledPrimeRoot_norm, one_pow, mul_one]
    norm_num [complexUnitPhase_norm]

/-- The literal actual sheet after a character substitution on its own prime torus. -/
def originalScheduledCharacterSheetPolynomial (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (j : Fin (originalReflectedOrderSchedule bound i.val))
    (g : OriginalScheduledPrimeTorus bound i.val) : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  originalPhasedPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
    ((originalScheduledParameterBlock bound i.val).parameter j)
    ((g.1.val : ℂ) ^ originalScheduledPrefixCoordinateDilation bound k i)
    (complexUnitPhase (-1 / 4) * (g.2.val : ℂ) ^ originalScheduledPrefixCoordinateDilation bound k i)

/-- Literal identity in the actual two-coordinate prime torus. -/
def originalScheduledPrimeTorusIdentity (bound : ℕ → ℕ) (i : ℕ) :
    OriginalScheduledPrimeTorus bound i := (1, 1)

/-- Exact actual character-substituted evaluation, with no polynomial representation input. -/
theorem originalScheduledCharacterSheetPolynomial_eval (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (j : Fin (originalReflectedOrderSchedule bound i.val))
    (g : OriginalScheduledPrimeTorus bound i.val) (Z W : ℂ) :
    originalPositiveTorusEvaluation Z W (originalScheduledCharacterSheetPolynomial bound k i j g) =
      originalPositiveTorusEvaluation ((g.1.val : ℂ) * Z) ((g.2.val : ℂ) * W)
        (originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
          ((originalScheduledParameterBlock bound i.val).parameter j)) := by
  rw [originalScheduledCharacterSheetPolynomial, originalPhasedPositiveSheetPolynomial_eval,
    ← originalPhasedPositiveSheetPolynomial_original, originalPhasedPositiveSheetPolynomial_eval]
  simp only [mul_pow]
  unfold sheetPolynomial
  ring

/-- The identity character recovers exactly the original sheet at its actual native scale. -/
theorem originalScheduledCharacterSheetPolynomial_one (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (j : Fin (originalReflectedOrderSchedule bound i.val)) :
    originalScheduledCharacterSheetPolynomial bound k i j (originalScheduledPrimeTorusIdentity bound i.val) =
      originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
        ((originalScheduledParameterBlock bound i.val).parameter j) := by
  simp [originalScheduledCharacterSheetPolynomial, originalScheduledPrimeTorusIdentity,
    originalPhasedPositiveSheetPolynomial_original]

/-- EVERY actual scheduled sheet and ALL its prime-torus translates are prime.
No irreducibility, primitive, root, phase or parameter certificate is supplied. -/
theorem originalScheduledCharacterSheetPolynomial_prime (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (j : Fin (originalReflectedOrderSchedule bound i.val))
    (g : OriginalScheduledPrimeTorus bound i.val) :
    Prime (originalScheduledCharacterSheetPolynomial bound k i j g) := by
  have hph := originalScheduledNativeCharacterPhases_norm bound k i g
  apply originalPhasedPositiveSheetPolynomial_prime _
    (originalScheduledPrefixCoordinateDilation_pos bound k i) _
    ((originalScheduledParameterBlock bound i.val).parameter_bounds j)
  · intro h; simp [h] at hph
  · intro h; simp [h] at hph

/-- EVERY actual original sheet is prime at its true mixed-prefix native dilation. -/
theorem originalScheduledPositiveSheetPolynomial_prime (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (j : Fin (originalReflectedOrderSchedule bound i.val)) :
    Prime (originalPositiveSheetPolynomial (originalScheduledPrefixCoordinateDilation bound k i)
      ((originalScheduledParameterBlock bound i.val).parameter j)) := by
  rw [← originalScheduledCharacterSheetPolynomial_one]
  exact originalScheduledCharacterSheetPolynomial_prime bound k i j (originalScheduledPrimeTorusIdentity bound i.val)

/-- Within one actual block, associates identify BOTH the sheet and the full native character. -/
theorem originalScheduledCharacterSheetPolynomial_associated_iff (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (j l : Fin (originalReflectedOrderSchedule bound i.val))
    (g h : OriginalScheduledPrimeTorus bound i.val) :
    Associated (originalScheduledCharacterSheetPolynomial bound k i j g)
      (originalScheduledCharacterSheetPolynomial bound k i l h) ↔ j = l ∧ g = h := by
  have hg := originalScheduledNativeCharacterPhases_norm bound k i g
  have hh := originalScheduledNativeCharacterPhases_norm bound k i h
  rw [originalScheduledCharacterSheetPolynomial, originalScheduledCharacterSheetPolynomial,
    originalPhasedPositiveSheetPolynomial_associated_iff _ _
      (originalScheduledPrefixCoordinateDilation_pos bound k i)
      (originalScheduledPrefixCoordinateDilation_pos bound k i) _ _
      ((originalScheduledParameterBlock bound i.val).parameter_bounds j).1
      ((originalScheduledParameterBlock bound i.val).parameter_bounds l).1 _ _ _ _ hg.1 hh.1]
  constructor
  · rintro ⟨_, hparam, hfirst, hsecond⟩
    have hcop := originalScheduledPrefixCoordinateDilation_coprime bound k i
    have h1 := originalRootOfUnity_native_power_injective _ _ hcop hfirst
    have h2 := originalRootOfUnity_native_power_injective _ _ hcop
      (mul_left_cancel₀ originalQuarterPhase_ne_zero hsecond)
    exact ⟨(originalScheduledParameterBlock bound i.val).injective hparam, Prod.ext h1 h2⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Different actual blocks have no common nonunit divisor between ANY translated sheets. -/
theorem originalScheduledCharacterSheetPolynomial_other_block_isRelPrime
    (bound : ℕ → ℕ) (k : ℕ) (i t : Fin k) (hit : i ≠ t)
    (j : Fin (originalReflectedOrderSchedule bound i.val))
    (l : Fin (originalReflectedOrderSchedule bound t.val))
    (g : OriginalScheduledPrimeTorus bound i.val) (h : OriginalScheduledPrimeTorus bound t.val) :
    IsRelPrime (originalScheduledCharacterSheetPolynomial bound k i j g)
      (originalScheduledCharacterSheetPolynomial bound k t l h) := by
  have hg := originalScheduledNativeCharacterPhases_norm bound k i g
  have hh := originalScheduledNativeCharacterPhases_norm bound k t h
  apply originalPhasedPositiveSheetPolynomial_isRelPrime_of_dilation_ne _ _
    (originalScheduledPrefixCoordinateDilation_pos bound k i)
    (originalScheduledPrefixCoordinateDilation_pos bound k t)
    (fun he => hit (originalScheduledPrefixCoordinateDilation_injective bound k he)) _ _
    ((originalScheduledParameterBlock bound i.val).parameter_bounds j)
    ((originalScheduledParameterBlock bound t.val).parameter_bounds l) _ _ _ _ hg.1 hh.1
  · intro he; simp [he] at hg
  · intro he; simp [he] at hh

/-- Distinct sheet/character labels within the actual full orbit have no common nonunit divisor. -/
theorem originalScheduledCharacterSheetPolynomial_same_block_isRelPrime
    (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (j l : Fin (originalReflectedOrderSchedule bound i.val))
    (g h : OriginalScheduledPrimeTorus bound i.val) (hne : j ≠ l ∨ g ≠ h) :
    IsRelPrime (originalScheduledCharacterSheetPolynomial bound k i j g)
      (originalScheduledCharacterSheetPolynomial bound k i l h) := by
  have hp := (originalScheduledCharacterSheetPolynomial_prime bound k i j g).irreducible
  have hq := (originalScheduledCharacterSheetPolynomial_prime bound k i l h).irreducible
  apply hp.isRelPrime_iff_not_dvd.mpr
  intro hdvd
  have he := (originalScheduledCharacterSheetPolynomial_associated_iff bound k i j l g h).mp
    (hp.associated_of_dvd hq hdvd)
  exact hne.elim (fun h => h he.1) (fun h => h he.2)

end
end MeyerGeneralProblem.StrongParity
