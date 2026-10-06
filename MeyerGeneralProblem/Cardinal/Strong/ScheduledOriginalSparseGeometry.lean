module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixLiteralRecovery

@[expose] public section

/-! Literal sparse integer submodules of the actual finite-prefix carrier.
Both signs, axes, the origin and the shared coarse cone are retained. No sparse
support or prime-coprimality certificate is a final actual-prefix input. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The literal simultaneous integer dilation of BOTH native coordinates. -/
def originalIntegerCoordinateDilation (d : ℕ) : (ℤ × ℤ) →+ (ℤ × ℤ) where
  toFun z := ((d : ℤ) * z.1, (d : ℤ) * z.2)
  map_zero' := by simp
  map_add' z w := by simp only [Prod.fst_add, Prod.snd_add, mul_add, Prod.mk_add_mk]

/-- All actual distinct block primes are coprime, supplied by the scheduled program. -/
theorem originalScheduledBlockPrimes_coprime (bound : ℕ → ℕ) (i j : ℕ) (hij : i ≠ j) :
    Nat.Coprime (originalReflectedPrimeSchedule bound i) (originalReflectedPrimeSchedule bound j) := by
  apply (originalReflectedSchedule_spec bound i).1.coprime_iff_not_dvd.mpr
  intro h
  have he := (Nat.prime_dvd_prime_iff_eq (originalReflectedSchedule_spec bound i).1
    (originalReflectedSchedule_spec bound j).1).mp h
  exact hij (originalPrivatePrimeSchedule_injective (originalReflectedWindowBounds bound) he)

/-- EVERY other actual prime divides a block's common-coordinate dilation. -/
theorem originalScheduledOtherPrime_dvd_coordinateDilation (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) : originalReflectedPrimeSchedule bound i.val ∣
      originalScheduledPrefixCoordinateDilation bound k j := by
  have hc := originalScheduledBlockPrimes_coprime bound i.val j.val
    (fun h => hij (Fin.ext h))
  apply hc.dvd_of_dvd_mul_right
  rw [originalScheduledPrefixCoordinateDilation_mul_prime]
  exact originalScheduledBlockPrime_dvd_prefix bound k i

/-- The actual common-label embedding preserves the ORIGINAL private frequency exactly. -/
theorem originalScheduledPrefixFrequency_coordinateDilation (bound : ℕ → ℕ) (k : ℕ)
    (i : Fin k) (z : ℤ × ℤ) :
    originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k))
        (originalIntegerCoordinateDilation (originalScheduledPrefixCoordinateDilation bound k i) z) =
      originalScaledModuleFrequencyHom (originalPrivateScale (originalReflectedPrimeSchedule bound i.val)) z := by
  change (((((originalScheduledPrefixCoordinateDilation bound k i : ℤ) * z.1 : ℤ) : ℝ) +
    beta * (((originalScheduledPrefixCoordinateDilation bound k i : ℤ) * z.2 : ℤ) : ℝ)) /
      originalPrivateScale (originalScheduledPrefixDenominator bound k)) =
    ((z.1 : ℝ) + beta * (z.2 : ℝ)) / originalPrivateScale (originalReflectedPrimeSchedule bound i.val)
  push_cast
  calc
    _ = ((originalScheduledPrefixCoordinateDilation bound k i : ℝ) /
        originalPrivateScale (originalScheduledPrefixDenominator bound k)) *
          ((z.1 : ℝ) + beta * (z.2 : ℝ)) := by ring
    _ = (1 / originalPrivateScale (originalReflectedPrimeSchedule bound i.val)) *
          ((z.1 : ℝ) + beta * (z.2 : ℝ)) := by
      rw [originalScheduledPrefixCoordinateDilation_ratio]
    _ = _ := by ring

/-- EVERY real point of a private cone has an actual integer module label. -/
theorem originalPrivateSpectralCone_subset_module (m : ℕ) (hm : 0 < m) :
    (originalPrivateSpectralCone m hm).carrier ⊆
      Set.range (originalScaledModuleFrequencyHom (originalPrivateScale m)) := by
  rintro x ⟨y, hy, rfl⟩
  have hy' : y ∈ translatedConeSet 0 0 := by
    rw [translatedConeSet_zero]
    exact hy
  obtain ⟨p, q, hy, _⟩ := (translatedConeSet_iff 0 0 y).mp hy'
  refine ⟨(p, q), ?_⟩
  simp only [originalScaledModuleFrequencyHom_apply, originalScaledModuleFrequency, hy,
    originalPrivateScale, div_eq_mul_inv, mul_comm]

/-- Every allowed private spectral point has BOTH common coordinates dilated by its block factor. -/
theorem originalScheduledPrivateSpectral_common_label (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (z : ℤ × ℤ)
    (hz : originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z ∈
      (originalScheduledPrivateSpectralCarrier bound i.val).carrier) :
    ∃ w : ℤ × ℤ, originalIntegerCoordinateDilation
      (originalScheduledPrefixCoordinateDilation bound k i) w = z := by
  obtain ⟨w, hw⟩ := originalPrivateSpectralCone_subset_module _ (originalScheduledBlockPrime_pos bound i.val) hz.1
  refine ⟨w, originalScaledModuleFrequencyHom_injective _
    (originalPrivateScale_pos _ (originalScheduledPrefixDenominator_pos bound k)).ne' ?_⟩
  rw [originalScheduledPrefixFrequency_coordinateDilation]
  exact hw

end
end MeyerGeneralProblem.StrongParity
