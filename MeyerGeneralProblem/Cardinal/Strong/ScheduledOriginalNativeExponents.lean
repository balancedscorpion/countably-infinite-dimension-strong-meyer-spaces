module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalAllBlockSplitting

@[expose] public section

/-! Actual private invariance forces EVERY nonzero original exponent to be a
multiple of the actual native dilation. The primitive roots, their orders and
all prime-product identities are supplied internally, without a support oracle. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The exact integer torus character on a genuine positive native label. -/
theorem originalIntegerTorusCharacter_native_value (ζ η : ℂˣ) (n : ℕ × ℕ) :
    (originalIntegerTorusCharacter ζ η
      (Multiplicative.ofAdd (originalNativeIntegerEmbedding n)) : ℂ) =
      (ζ : ℂ) ^ n.1 * (η : ℂ) ^ n.2 := by
  change ((ζ ^ (n.1 : ℤ) * η ^ (n.2 : ℤ) : ℂˣ) : ℂ) = _
  simp only [Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]

/-- Every actual prime-invariant positive coefficient has BOTH exponents
divisible by that actual prime; the two primitive rotations are constructed. -/
theorem originalScheduledPrimeInvariant_coefficient_dvd (bound : ℕ → ℕ) (j : ℕ)
    (u : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hinv : ∀ g : OriginalScheduledPrimeTorus bound j,
      originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j g) u = u)
    (n : ℕ × ℕ) (hn : u.coeff n ≠ 0) :
    originalReflectedPrimeSchedule bound j ∣ n.1 ∧ originalReflectedPrimeSchedule bound j ∣ n.2 := by
  have h₁ := congrArg (fun p : AddMonoidAlgebra ℂ (ℕ × ℕ) => p.coeff n)
    (hinv (originalScheduledPrimitiveRoot bound j, 1))
  have h₂ := congrArg (fun p : AddMonoidAlgebra ℂ (ℕ × ℕ) => p.coeff n)
    (hinv (1, originalScheduledPrimitiveRoot bound j))
  change (originalPositiveCharacterTwist
    (originalIntegerTorusCharacter (originalScheduledPrimitiveRoot bound j).val 1) u).coeff n = u.coeff n at h₁
  change (originalPositiveCharacterTwist
    (originalIntegerTorusCharacter 1 (originalScheduledPrimitiveRoot bound j).val) u).coeff n = u.coeff n at h₂
  rw [originalPositiveCharacterTwist_coefficient, originalIntegerTorusCharacter_native_value] at h₁ h₂
  simp only [Units.val_one, one_pow, mul_one, one_mul] at h₁ h₂
  have hp₁ : ((originalScheduledPrimitiveRoot bound j).val : ℂ) ^ n.1 = 1 :=
    (mul_right_cancel₀ hn) (h₁.trans (one_mul (u.coeff n)).symm)
  have hp₂ : ((originalScheduledPrimitiveRoot bound j).val : ℂ) ^ n.2 = 1 :=
    (mul_right_cancel₀ hn) (h₂.trans (one_mul (u.coeff n)).symm)
  exact ⟨(originalScheduledPrimitiveRoot_isPrimitive bound j).dvd_of_pow_eq_one n.1 hp₁,
    (originalScheduledPrimitiveRoot_isPrimitive bound j).dvd_of_pow_eq_one n.2 hp₂⟩

/-- Pairwise natural coprimality combines ALL individual divisibilities,
including the empty product. This does not assume a positive Bezout identity. -/
theorem originalNat_pairwise_prod_dvd {ι : Type*} (s : Finset ι) (p : ι → ℕ) (n : ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (p i) (p j))
    (hdiv : ∀ i ∈ s, p i ∣ n) : (∏ i ∈ s, p i) ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hc : Nat.Coprime (p a) (∏ i ∈ s, p i) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro i hi
      exact hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (ne_of_mem_of_not_mem hi ha).symm
    apply hc.mul_dvd_of_dvd_of_dvd (hdiv a (Finset.mem_insert_self a s))
    exact ih (fun i hi j hj hij => hcop i (Finset.mem_insert_of_mem hi) j
      (Finset.mem_insert_of_mem hj) hij) (fun i hi => hdiv i (Finset.mem_insert_of_mem hi))

/-- ALL other-private-group invariances force EVERY nonzero selected exponent
to be a multiple of its ACTUAL coordinate dilation, with all arithmetic internal. -/
theorem originalScheduledPrivateInvariant_support_dilation (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (u : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hinv : ∀ (j : Fin k), i ≠ j → ∀ g : OriginalScheduledPrimeTorus bound j.val,
      originalPositiveCharacterTwist (originalScheduledPrimeCharacter bound j.val g) u = u)
    (n : ℕ × ℕ) (hn : n ∈ u.coeff.support) :
    originalScheduledPrefixCoordinateDilation bound k i ∣ n.1 ∧
      originalScheduledPrefixCoordinateDilation bound k i ∣ n.2 := by
  classical
  have hc : ∀ a ∈ Finset.univ.erase i, ∀ b ∈ Finset.univ.erase i,
      a ≠ b → Nat.Coprime (originalReflectedPrimeSchedule bound a.val) (originalReflectedPrimeSchedule bound b.val) := by
    intro a _ b _ hab
    exact originalScheduledBlockPrimes_coprime bound a.val b.val (fun he => hab (Fin.ext he))
  have hd (j : Fin k) (hj : j ∈ Finset.univ.erase i) :
      originalReflectedPrimeSchedule bound j.val ∣ n.1 ∧ originalReflectedPrimeSchedule bound j.val ∣ n.2 :=
    originalScheduledPrimeInvariant_coefficient_dvd bound j.val u
      (hinv j (Finset.mem_erase.mp hj).1.symm) n (Finsupp.mem_support_iff.mp hn)
  rw [originalScheduledPrefixCoordinateDilation_eq_other_product]
  exact ⟨originalNat_pairwise_prod_dvd _ _ _ hc (fun j hj => (hd j hj).1),
    originalNat_pairwise_prod_dvd _ _ _ hc (fun j hj => (hd j hj).2)⟩

end
end MeyerGeneralProblem.StrongParity
