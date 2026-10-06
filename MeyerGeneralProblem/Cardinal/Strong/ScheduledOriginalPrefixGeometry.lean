module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalCommonCarrier
public import MeyerGeneralProblem.Cardinal.Strong.PositiveConeClearingGeometry

@[expose] public section

/-! Actual complete finite prefixes and their internally chosen common scale.
Every allowed point of each private physical and spectral carrier is retained,
including coarse points and zero coefficients. The common natural denominator
is the product of block primes, with every integer coordinate dilation proved. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Product of the actual BLOCK primes; the empty prefix has denominator one. -/
def originalScheduledPrefixDenominator (bound : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∏ i : Fin k, originalReflectedPrimeSchedule bound i.val

/-- The empty prefix uses the literal unit denominator. -/
@[simp] theorem originalScheduledPrefixDenominator_zero (bound : ℕ → ℕ) :
    originalScheduledPrefixDenominator bound 0 = 1 := by simp [originalScheduledPrefixDenominator]

/-- The common denominator is internally positive for EVERY finite prefix. -/
theorem originalScheduledPrefixDenominator_pos (bound : ℕ → ℕ) (k : ℕ) :
    0 < originalScheduledPrefixDenominator bound k := by
  unfold originalScheduledPrefixDenominator
  exact Finset.prod_pos (fun i _ => originalScheduledBlockPrime_pos bound i.val)

/-- Every complete block's actual prime divides the chosen common denominator. -/
theorem originalScheduledBlockPrime_dvd_prefix (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    originalReflectedPrimeSchedule bound i.val ∣ originalScheduledPrefixDenominator bound k := by
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- The actual integer coordinate dilation for a whole block, common to ALL its sheets. -/
def originalScheduledPrefixCoordinateDilation (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) : ℕ :=
  originalScheduledPrefixDenominator bound k / originalReflectedPrimeSchedule bound i.val

/-- Exact integer factorisation of the literal common denominator. -/
theorem originalScheduledPrefixCoordinateDilation_mul_prime (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    originalScheduledPrefixCoordinateDilation bound k i * originalReflectedPrimeSchedule bound i.val =
      originalScheduledPrefixDenominator bound k :=
  Nat.div_mul_cancel (originalScheduledBlockPrime_dvd_prefix bound k i)

/-- Positive coordinate dilation is supplied internally. -/
theorem originalScheduledPrefixCoordinateDilation_pos (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    0 < originalScheduledPrefixCoordinateDilation bound k i := by
  have he := originalScheduledPrefixCoordinateDilation_mul_prime bound k i
  by_contra h
  have hz : originalScheduledPrefixCoordinateDilation bound k i = 0 := Nat.eq_zero_of_not_pos h
  rw [hz, zero_mul] at he
  exact (originalScheduledPrefixDenominator_pos bound k).ne' he.symm

/-- Exact ratio of the common native scale and every original block scale. -/
theorem originalScheduledPrefixCoordinateDilation_ratio (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    (originalScheduledPrefixCoordinateDilation bound k i : ℝ) /
      originalPrivateScale (originalScheduledPrefixDenominator bound k) =
        1 / originalPrivateScale (originalReflectedPrimeSchedule bound i.val) := by
  have he : (originalScheduledPrefixCoordinateDilation bound k i : ℝ) *
      (originalReflectedPrimeSchedule bound i.val : ℝ) =
        (originalScheduledPrefixDenominator bound k : ℝ) := by
    exact_mod_cast originalScheduledPrefixCoordinateDilation_mul_prime bound k i
  apply (div_eq_div_iff
    (originalPrivateScale_pos _ (originalScheduledPrefixDenominator_pos bound k)).ne'
    (originalPrivateScale_pos _ (originalScheduledBlockPrime_pos bound i.val)).ne').mpr
  simp only [originalPrivateScale, one_mul]
  calc
    _ = parityDilationUnit * ((originalScheduledPrefixCoordinateDilation bound k i : ℝ) *
      (originalReflectedPrimeSchedule bound i.val : ℝ)) := by ring
    _ = _ := by rw [he]

/-- Whole common native cone at the actual finite-prefix denominator. -/
def originalScheduledPrefixCone (bound : ℕ → ℕ) (k : ℕ) : LocallyFiniteCarrier :=
  scaledTranslatedConeCarrier 0 0 (originalPrivateScale (originalScheduledPrefixDenominator bound k))
    (originalPrivateScale_pos _ (originalScheduledPrefixDenominator_pos bound k))

/-- Whole private cones embed at a divisible common scale, including BOTH axes and zero. -/
theorem originalPrivateSpectralCone_subset_divisible (m M : ℕ) (hm : 0 < m) (hM : 0 < M)
    (hd : m ∣ M) : (originalPrivateSpectralCone m hm).carrier ⊆
      (scaledTranslatedConeCarrier 0 0 (originalPrivateScale M) (originalPrivateScale_pos M hM)).carrier := by
  obtain ⟨d, rfl⟩ := hd
  rintro x ⟨y, hy, rfl⟩
  refine ⟨(d : ℝ) * y, ?_, ?_⟩
  · change (d : ℝ) * y ∈ translatedConeSet 0 0
    rw [translatedConeSet_zero]
    exact originalSpectralConeSet_nat_mul d y hy
  · have hc := parityDilationUnit_pos.ne'
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hdR : (d : ℝ) ≠ 0 := by
      have hdp : 0 < d := Nat.pos_of_mul_pos_left hM
      exact_mod_cast hdp.ne'
    simp only [originalPrivateScale, Nat.cast_mul]
    field_simp

/-- Every actual private spectral carrier lies in the complete common native cone. -/
theorem originalScheduledPrivateSpectralCarrier_subset_prefixCone
    (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    (originalScheduledPrivateSpectralCarrier bound i.val).carrier ⊆
      (originalScheduledPrefixCone bound k).carrier := by
  intro x hx
  apply originalPrivateSpectralCone_subset_divisible _ _ (originalScheduledBlockPrime_pos bound i.val)
    (originalScheduledPrefixDenominator_pos bound k) (originalScheduledBlockPrime_dvd_prefix bound k i)
  exact hx.1

/-- ALL complete undeleted physical roots in the finite prefix. -/
def originalScheduledPrefixRootSet (bound : ℕ → ℕ) (k : ℕ) : Set ℝ :=
  ⋃ i : Fin k, (originalScheduledFullPhysicalCarrier bound i.val).carrier

/-- Actual whole finite mixed common carrier, retaining every original allowed point. -/
def originalScheduledPrefixCarrier (bound : ℕ → ℕ) (k : ℕ) : LocallyFiniteCarrier where
  carrier := originalSharedCoarseCone.carrier ∪ ⋃ i : Fin k,
    (originalScheduledPrivatePhysicalCarrier bound i.val).carrier ∪
      (originalScheduledPrivateSpectralCarrier bound i.val).carrier
  finite_inter_Icc a b := by
    rw [Set.union_inter_distrib_right, Set.iUnion_inter]
    apply (originalSharedCoarseCone.finite_inter_Icc a b).union
    apply Set.finite_iUnion
    intro i
    rw [Set.union_inter_distrib_right]
    exact ((originalScheduledPrivatePhysicalCarrier bound i.val).finite_inter_Icc a b).union
      ((originalScheduledPrivateSpectralCarrier bound i.val).finite_inter_Icc a b)

/-- The empty mixed prefix retains precisely the fixed whole coarse cone. -/
@[simp] theorem originalScheduledPrefixCarrier_zero (bound : ℕ → ℕ) :
    originalScheduledPrefixCarrier bound 0 = originalSharedCoarseCone := by
  apply LocallyFiniteCarrier.ext
  simp [originalScheduledPrefixCarrier]

/-- WHOLE mixed support is internally covered by complete roots and the common native cone. -/
theorem originalScheduledPrefixCarrier_subset_roots_union_cone (bound : ℕ → ℕ) (k : ℕ) :
    (originalScheduledPrefixCarrier bound k).carrier ⊆ originalScheduledPrefixRootSet bound k ∪
      (originalScheduledPrefixCone bound k).carrier := by
  rintro x (hx | hx)
  · exact Or.inr ((originalPrivateSpectralCone_subset_divisible 1 _ (by norm_num)
      (originalScheduledPrefixDenominator_pos bound k) (one_dvd _))
      ((originalSharedCoarseCone_subset_private 1 (by norm_num)) hx))
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rcases hi with hi | hi
    · exact Or.inl (Set.mem_iUnion.mpr ⟨i, originalScheduledPrivatePhysicalCarrier_subset_full _ _ hi⟩)
    · exact Or.inr (originalScheduledPrivateSpectralCarrier_subset_prefixCone bound k i hi)

/-- The finite carrier is an actual prefix of the WHOLE infinite common carrier. -/
theorem originalScheduledPrefixCarrier_subset_common (bound : ℕ → ℕ) (k : ℕ) :
    (originalScheduledPrefixCarrier (originalCommonWindowBounds bound) k).carrier ⊆
      (originalScheduledCommonCarrier bound).carrier := by
  rintro x (hx | hx)
  · rw [originalScheduledCommonCarrier_carrier]
    exact Or.inl hx
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hi.elim (fun h => originalScheduledPrivatePhysicalCarrier_subset_common bound i.val h)
      (fun h => originalScheduledPrivateSpectralCarrier_subset_common bound i.val h)

end
end MeyerGeneralProblem.StrongParity
