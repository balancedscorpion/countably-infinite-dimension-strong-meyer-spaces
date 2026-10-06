module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalNativeReconstruction

@[expose] public section

/-! Literal intersections of the actual private cones and mixed prefix.
Coprime actual scales leave exactly the shared coarse cone. Complete full
physical roots meet the original prefix only on their own allowed carrier;
each actual noncoarse deleted head point is absent from the whole prefix. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Absolute original private label values recover the full positive native
coordinates, including zero and both signed axes. -/
theorem originalPrivateSpectralLabelValue_abs_coordinates (m : ℕ) (hm : 0 < m)
    (label : spectralConeIndex) :
    positiveConeFrequency (spectralConeIndexCoordinates label) =
      originalPrivateScale m * |originalPrivateSpectralLabelValue m label| := by
  have hp := originalPrivateScale_pos m hm
  change positiveConeFrequency (spectralConeIndexCoordinates label) =
    originalPrivateScale m * |spectralConeIndexFrequency label / originalPrivateScale m|
  simp only [abs_div,
    abs_of_pos hp, spectralConeIndexFrequency_abs]
  exact (mul_div_cancel₀ _ hp.ne').symm

/-- For coprime positive scales the WHOLE private cones intersect in exactly
the original shared coarse cone; no coefficient support is selected. -/
theorem originalPrivateSpectralCone_inter_coprime (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hcop : Nat.Coprime m n) :
    (originalPrivateSpectralCone m hm).carrier ∩ (originalPrivateSpectralCone n hn).carrier =
      originalSharedCoarseCone.carrier := by
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    obtain ⟨a, ha⟩ := originalPrivateSpectralCone_label_surjective m hm x hx
    obtain ⟨b, hb⟩ := originalPrivateSpectralCone_label_surjective n hn x hy
    have he : positiveConeFrequency
        (n * (spectralConeIndexCoordinates a).1, n * (spectralConeIndexCoordinates a).2) =
        positiveConeFrequency
        (m * (spectralConeIndexCoordinates b).1, m * (spectralConeIndexCoordinates b).2) := by
      rw [positiveConeFrequency_nat_mul, positiveConeFrequency_nat_mul,
        originalPrivateSpectralLabelValue_abs_coordinates m hm a,
        originalPrivateSpectralLabelValue_abs_coordinates n hn b, ha, hb]
      simp only [originalPrivateScale]
      ring
    have hcoord := positiveConeFrequency_injective he
    rw [← ha, originalPrivateSpectralLabelValue_coarse_divisibility m hm a]
    constructor
    · apply hcop.dvd_of_dvd_mul_left
      exact ⟨(spectralConeIndexCoordinates b).1, congrArg Prod.fst hcoord⟩
    · apply hcop.dvd_of_dvd_mul_left
      exact ⟨(spectralConeIndexCoordinates b).2, congrArg Prod.snd hcoord⟩
  · intro hx
    exact ⟨originalSharedCoarseCone_subset_private m hm hx,
      originalSharedCoarseCone_subset_private n hn hx⟩

/-- Different ACTUAL scheduled full private cones have exactly the coarse
intersection, derived from the implemented pairwise coprime block primes. -/
theorem originalScheduledFullPrivateCones_inter (bound : ℕ → ℕ) (i j : ℕ) (hij : i ≠ j) :
    (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i)
      (originalScheduledBlockPrime_pos bound i)).carrier ∩
    (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound j)
      (originalScheduledBlockPrime_pos bound j)).carrier = originalSharedCoarseCone.carrier :=
  originalPrivateSpectralCone_inter_coprime _ _ _ _ (originalScheduledBlockPrimes_coprime bound i j hij)

/-- EVERY original allowed private physical point is retained by the whole prefix. -/
theorem originalScheduledPrivatePhysicalCarrier_subset_prefix (bound : ℕ → ℕ) (k : ℕ) (i : Fin k) :
    (originalScheduledPrivatePhysicalCarrier bound i.val).carrier ⊆
      (originalScheduledPrefixCarrier bound k).carrier :=
  fun _ hx => Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inl hx⟩)

/-- The complete original shared cone is retained at the actual common prefix scale. -/
theorem originalSharedCoarseCone_subset_prefixCone (bound : ℕ → ℕ) (k : ℕ) :
    originalSharedCoarseCone.carrier ⊆ (originalScheduledPrefixCone bound k).carrier :=
  fun _ hx => originalPrivateSpectralCone_subset_divisible 1 _ (by norm_num)
    (originalScheduledPrefixDenominator_pos bound k) (one_dvd _)
    (originalSharedCoarseCone_subset_private 1 (by norm_num) hx)

/-- On EVERY actual full physical block, original prefix membership is
EXACTLY its own allowed physical membership; other blocks and cones cannot add rows. -/
theorem originalScheduledFullPhysicalCarrier_prefix_iff (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (x : ℝ) (hx : x ∈ (originalScheduledFullPhysicalCarrier bound i.val).carrier) :
    x ∈ (originalScheduledPrefixCarrier bound k).carrier ↔
      x ∈ (originalScheduledPrivatePhysicalCarrier bound i.val).carrier := by
  have hroot := originalScheduledFullPhysicalCarrier_subset_prefixRoots bound k i hx
  have hnc : x ∉ (originalScheduledPrefixCone bound k).carrier :=
    fun hc => Set.disjoint_left.mp (originalScheduledPrefixFullRoots_disjoint_cone bound k) hroot hc
  constructor
  · rintro (hc | hp)
    · exact False.elim (hnc (originalSharedCoarseCone_subset_prefixCone bound k hc))
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
      rcases hj with hj | hj
      · have hji : j = i := by
          by_contra h
          exact Set.disjoint_left.mp (originalScheduledFullPhysicalCarrier_pairwise_disjoint bound
            (fun he => h (Fin.ext he)))
            (originalScheduledPrivatePhysicalCarrier_subset_full bound j.val hj) hx
        simpa only [hji] using hj
      · exact False.elim (hnc (originalScheduledPrivateSpectralCarrier_subset_prefixCone bound k j hj))
  · exact fun hx => originalScheduledPrivatePhysicalCarrier_subset_prefix bound k i hx

/-- Every deleted ACTUAL private noncoarse head point is absent from the
whole original prefix, including all other blocks and the retained coarse cone. -/
theorem originalScheduledPrivateHead_not_mem_prefix (bound : ℕ → ℕ) (k : ℕ) (i : Fin k)
    (x : ℝ)
    (hx : x ∈ (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound i.val)
      (originalScheduledBlockPrime_pos bound i.val)).carrier)
    (hh : x ∈ originalPrivateGeometricHead (originalReflectedOrderSchedule bound i.val)
      (originalReflectedPrimeSchedule bound i.val)) :
    x ∉ (originalScheduledPrefixCarrier bound k).carrier := by
  have hc := originalScheduledFullPrivateCone_subset_prefixCone bound k i hx
  rintro (hcoarse | hp)
  · exact hh.2 hcoarse
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    rcases hj with hj | hj
    · exact Set.disjoint_left.mp (originalScheduledPrefixFullRoots_disjoint_cone bound k)
        (originalScheduledFullPhysicalCarrier_subset_prefixRoots bound k j
          (originalScheduledPrivatePhysicalCarrier_subset_full bound j.val hj)) hc
    · by_cases hji : j = i
      · subst j
        exact hj.2 hh
      · apply hh.2
        rw [← originalScheduledFullPrivateCones_inter bound i.val j.val
          (fun he => hji (Fin.ext he).symm)]
        exact ⟨hx, hj.1⟩

end
end MeyerGeneralProblem.StrongParity
