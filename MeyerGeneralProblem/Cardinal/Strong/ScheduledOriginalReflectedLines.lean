module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrivateRows

@[expose] public section

/-! Complete actual finite-prefix mixed source-line exhaustion. Only the
allowed CONE part is reflected: the original physical carrier is not assumed
symmetric. Genuine Fourier inversion and BOTH SAME original exponents supply
the companion's private-line classification internally. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The ENTIRE original shared coarse cone is symmetric, including zero. -/
theorem originalSharedCoarseCone_neg_iff (x : ℝ) :
    -x ∈ originalSharedCoarseCone.carrier ↔ x ∈ originalSharedCoarseCone.carrier := by
  have h : ∀ x ∈ originalSharedCoarseCone.carrier, -x ∈ originalSharedCoarseCone.carrier := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, (originalSpectralConeSet_neg_iff y).mpr hy, by ring⟩
  exact ⟨fun hx => by simpa only [neg_neg] using h (-x) hx, h x⟩

/-- The ACTUAL full private cone retains both signs of every point. -/
theorem originalPrivateSpectralCone_neg_iff (m : ℕ) (hm : 0 < m) (x : ℝ) :
    -x ∈ (originalPrivateSpectralCone m hm).carrier ↔
      x ∈ (originalPrivateSpectralCone m hm).carrier := by
  have h : ∀ x ∈ (originalPrivateSpectralCone m hm).carrier,
      -x ∈ (originalPrivateSpectralCone m hm).carrier := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, (originalSpectralConeSet_neg_iff y).mpr hy, by ring⟩
  exact ⟨fun hx => by simpa only [neg_neg] using h (-x) hx, h x⟩

/-- Reflection preserves the entire original noncoarse head deletion. -/
theorem originalPrivateGeometricHead_neg_iff (s m : ℕ) (x : ℝ) :
    -x ∈ originalPrivateGeometricHead s m ↔ x ∈ originalPrivateGeometricHead s m := by
  simp only [originalPrivateGeometricHead, Set.mem_ofPred_eq, abs_neg, originalSharedCoarseCone_neg_iff]

/-- The actual allowed private spectral carrier, after ALL deletions, is symmetric. -/
theorem originalScheduledPrivateSpectralCarrier_neg_iff (bound : ℕ → ℕ) (i : ℕ) (x : ℝ) :
    -x ∈ (originalScheduledPrivateSpectralCarrier bound i).carrier ↔
      x ∈ (originalScheduledPrivateSpectralCarrier bound i).carrier := by
  change (-x ∈ (originalPrivateSpectralCone _ _).carrier ∧ -x ∉ originalPrivateGeometricHead _ _) ↔
    (x ∈ (originalPrivateSpectralCone _ _).carrier ∧ x ∉ originalPrivateGeometricHead _ _)
  rw [originalPrivateSpectralCone_neg_iff, originalPrivateGeometricHead_neg_iff]

/-- Only the allowed CONE part of the original mixed prefix is symmetric;
full physical roots are excluded using their actual disjointness from the cone. -/
theorem originalScheduledPrefixCarrier_neg_of_cone (bound : ℕ → ℕ) (k : ℕ) (x : ℝ)
    (hx : x ∈ (originalScheduledPrefixCarrier bound k).carrier)
    (hc : x ∈ (originalScheduledPrefixCone bound k).carrier) :
    -x ∈ (originalScheduledPrefixCarrier bound k).carrier := by
  rcases hx with hx | hx
  · exact Or.inl ((originalSharedCoarseCone_neg_iff x).mpr hx)
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rcases hi with hi | hi
    · exact False.elim (Set.disjoint_left.mp (originalScheduledPrefixFullRoots_disjoint_cone bound k)
        (originalScheduledFullPhysicalCarrier_subset_prefixRoots bound k i
          (originalScheduledPrivatePhysicalCarrier_subset_full bound i.val hi)) hc)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inr
        ((originalScheduledPrivateSpectralCarrier_neg_iff bound i.val x).mpr hi)⟩)

/-- A genuine original cone-supported record reflects back onto the SAME
original mixed carrier with the SAME original weighted-TV exponent. -/
theorem originalScheduledPrefix_fourier_square_strong_of_cone (bound : ℕ → ℕ) (k M : ℕ)
    (C : TemperedDistribution ℝ ℂ)
    (hC : C ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hc : AtomicOnCarrier (originalScheduledPrefixCone bound k) C) :
    𝓕 (𝓕 C) ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M := by
  let S := originalScheduledPrefixCarrier bound k
  let A := S.carrier ∩ (originalScheduledPrefixCone bound k).carrier
  have ha : AtomicOnCarrier (S.restrict A Set.inter_subset_left) C := by
    apply (atomicOnCarrier_restrict_iff _ _ _ _).mpr
    refine ⟨hasLocallyAtomicAction_atomicOnCarrier _ _ hC.1, ?_⟩
    intro x hx
    exact atomic_isolation_eq_zero_off_other_carrier _ _ C
      (hasLocallyAtomicAction_atomicOnCarrier _ _ hC.1) hc x
      (fun h => hx ⟨x.property, h⟩)
  have hs := stronglyTemperedAtomicAtExponent_restrict S A Set.inter_subset_left M C ha hC
  have hr := stronglyTemperedAtomicAtExponent_fourier_fourier _ M C hs
  refine stronglyTemperedAtomicAtExponent_mono_carrier (T := 𝓕 (𝓕 C)) (N := M) ?_ hr
  rintro x ⟨y, hy, rfl⟩
  exact originalScheduledPrefixCarrier_neg_of_cone bound k y hy.1 hy.2

/-- The Fourier transform of the GENUINE companion has BOTH actual original
strong records, exchanging the original N and M without reflecting physical roots. -/
theorem originalScheduledPrefixRootSource_companion_fourier_both_strong (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    𝓕 (T - originalScheduledPrefixRootSource bound k N T hF) ∈
      stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N ∧
    𝓕 (𝓕 (T - originalScheduledPrefixRootSource bound k N T hF)) ∈
      stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M := by
  have h := originalScheduledPrefixRootSource_complement_both_original_strong bound k M N T hT hF
  exact ⟨h.2, originalScheduledPrefix_fourier_square_strong_of_cone bound k M _ h.1
    (originalScheduledPrefixRootSource_complement_atomicOnCone bound k M N T hT hF)⟩

/-- For an actual original strong pair already supported on FULL roots,
the genuine recovered root component is the WHOLE pair itself. -/
theorem originalScheduledPrefixRootSource_eq_self_onRoots (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N)
    (ha : AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k) T) :
    originalScheduledPrefixRootSource bound k N T hF = T := by
  have hρ := originalScheduledPrefixRootSource_atomicOnRoots bound k M N T hT hF
  have hdiff : AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k)
      (T - originalScheduledPrefixRootSource bound k N T hF) := by
    intro f hf
    change T f - originalScheduledPrefixRootSource bound k N T hF f = 0
    rw [ha f hf, hρ f hf, sub_self]
  apply atomic_eq_of_coefficients _ _ _ hρ ha
  intro x
  have hz := atomic_isolation_eq_zero_off_other_carrier _ _ _ hdiff
    (originalScheduledPrefixRootSource_complement_atomicOnCone bound k M N T hT hF) x
    (fun hc => Set.disjoint_left.mp (originalScheduledPrefixFullRoots_disjoint_cone bound k) x.property hc)
  exact (sub_eq_zero.mp hz).symm

/-- EVERY COMPLETE actual original prefix strongly tempered pair is a
finite sum of the actual scheduled source lines and their GENUINE inverse Fourier
transforms. No source, row, reflection, restriction or exhaustion certificate is input. -/
theorem originalScheduledPrefix_complete_mixed_private_lines (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ a b : Fin k → ℂ,
      T = (∑ i : Fin k, a i • originalScheduledPrivateLineSource bound i.val) +
        𝓕⁻ (∑ i : Fin k, b i • originalScheduledPrivateLineSource bound i.val) := by
  obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT.1
  obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hT.2
  have hM' : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M := hM
  have hN' : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N := hN
  let ρ := originalScheduledPrefixRootSource bound k N T hN'
  let Q := 𝓕 (T - ρ)
  obtain ⟨_, a, ha, _⟩ := originalScheduledPrefixRootSource_native_private_lines bound k M N T hM' hN'
  have hQ := originalScheduledPrefixRootSource_companion_fourier_both_strong bound k M N T hM' hN'
  obtain ⟨_, b, hb, _⟩ := originalScheduledPrefixRootSource_native_private_lines bound k N M Q hQ.1 hQ.2
  have hself := originalScheduledPrefixRootSource_eq_self_onRoots bound k N M Q hQ.1 hQ.2
    (originalScheduledPrefixRootSource_complement_fourier_atomicOnRoots bound k N T hN')
  rw [hself] at hb
  have hc : T - ρ = 𝓕⁻ (∑ i : Fin k, b i • originalScheduledPrivateLineSource bound i.val) := by
    rw [← hb]
    exact (FourierTransform.fourierInv_fourier_eq (T - ρ)).symm
  refine ⟨a, b, ?_⟩
  rw [← ha, ← hc]
  exact (add_sub_cancel _ _).symm

end
end MeyerGeneralProblem.StrongParity
