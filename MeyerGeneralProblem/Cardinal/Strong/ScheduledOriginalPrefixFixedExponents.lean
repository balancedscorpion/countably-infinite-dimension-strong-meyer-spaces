module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalReflectedLines

@[expose] public section

/-! SAME-original-exponent bounds for the actual finite mixed source lines.
Physical coefficients of each disjoint genuine source are sampled directly from
the whole original sum. The proved private mass obstruction kills every source
whose actual order exceeds that original exponent, in both Fourier orientations. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- Every genuinely private native source samples the WHOLE original sum's
physical variation at the SAME exponent M; no larger source exponent substitutes for M. -/
theorem originalScheduledNativeSource_private_physicalExponent_of_sum (bound : ℕ → ℕ) (k M : ℕ)
    (r : (i : Fin k) → productNumeratorIndex (originalReflectedOrderSchedule bound i.val) → ℂ)
    (hprivate : ∀ i : Fin k, originalScheduledNativeSource bound i.val (r i) ∈
      originalScheduledPrivateStrongPair bound i.val)
    (hsum : (∑ i : Fin k, originalScheduledNativeSource bound i.val (r i)) ∈
      stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (i : Fin k) :
    originalScheduledNativeSource bound i.val (r i) ∈
      stronglyTemperedAtomicAtExponent (originalScheduledPrivatePhysicalCarrier bound i.val) M := by
  obtain ⟨_, hl, _⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mp (hprivate i).1
  refine ⟨hl, ?_⟩
  have hincl := originalScheduledPrivatePhysicalCarrier_subset_prefix bound k i
  have hs := hsum.2.comp_injective (LocallyFiniteCarrier.inclusion hincl).injective
  convert! hs using 1
  funext x
  have hxfull := originalScheduledPrivatePhysicalCarrier_subset_full bound i.val x.property
  have hxroots := originalScheduledFullPhysicalCarrier_subset_prefixRoots bound k i hxfull
  have hxprefix := hincl x.property
  have he := extendedAtomicCoefficient_two_carriers
    (originalScheduledPrefixFullRootCarrier bound k) (originalScheduledPrefixCarrier bound k)
    (∑ j : Fin k, originalScheduledNativeSource bound j.val (r j))
    (originalScheduledNativeSource_sum_atomicOnRoots bound k r)
    (hasLocallyAtomicAction_atomicOnCarrier _ _ hsum.1) (x : ℝ)
  simp only [extendedAtomicCoefficient, dite_eq_left hxroots, dite_eq_left hxprefix] at he
  have hrow : (∑ j : Fin k, originalScheduledNativeSource bound j.val (r j))
      ((originalScheduledPrefixCarrier bound k).isolationSchwartz
        (LocallyFiniteCarrier.inclusion hincl x)) =
      originalScheduledNativeSource bound i.val (r i)
        ((originalScheduledPrivatePhysicalCarrier bound i.val).isolationSchwartz x) := by
    calc
      _ = (∑ j : Fin k, originalScheduledNativeSource bound j.val (r j))
          ((originalScheduledPrefixFullRootCarrier bound k).isolationSchwartz ⟨x, hxroots⟩) := he.symm
      _ = originalScheduledNativeSource bound i.val (r i)
          ((originalScheduledFullPhysicalCarrier bound i.val).isolationSchwartz ⟨x, hxfull⟩) :=
        originalScheduledNativeSource_sum_isolation bound k r i ⟨x, hxfull⟩
      _ = _ := isolationAction_eq_of_carrier_subset
        (originalScheduledPrivatePhysicalCarrier_subset_full bound i.val) _ hl x
  simp only [Function.comp_apply]
  unfold stronglyTemperedCoefficientTerm
  rw [hrow]
  rfl

/-- EVERY actual original finite-prefix root source is a sum of its actual
private lines, with each physical record at the ORIGINAL M and every order above M zero. -/
theorem originalScheduledPrefixRootSource_private_lines_original_bound (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    ∃ a : Fin k → ℂ,
      originalScheduledPrefixRootSource bound k N T hF =
        ∑ i : Fin k, a i • originalScheduledPrivateLineSource bound i.val ∧
      (∀ i : Fin k, a i • originalScheduledPrivateLineSource bound i.val ∈
        stronglyTemperedAtomicAtExponent (originalScheduledPrivatePhysicalCarrier bound i.val) M) ∧
      (∀ i : Fin k, M < originalReflectedOrderSchedule bound i.val → a i = 0) := by
  classical
  obtain ⟨r, a, ha, hr, hp⟩ := originalScheduledPrefixRootSource_native_private_lines bound k M N T hT hF
  have hsum : (∑ i : Fin k, originalScheduledNativeSource bound i.val (r i)) ∈
      stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M := by
    have h := (originalScheduledPrefixRootSource_both_original_strong bound k M N T hT hF).1
    rw [ha] at h
    simpa only [hr] using h
  have hstrong := originalScheduledNativeSource_private_physicalExponent_of_sum bound k M r hp hsum
  refine ⟨a, ha, ?_, ?_⟩
  · intro i
    rw [← hr i]
    exact hstrong i
  · intro i hi
    have hz : originalScheduledNativeSource bound i.val (r i) = 0 := by
      by_contra hn
      exact originalScheduledPrivateStrongPair_not_lowExponent bound i.val M hi _ (hp i) hn (hstrong i)
    rw [hr i] at hz
    exact (smul_eq_zero.mp hz).resolve_right (originalScheduledPrivateLineSource_ne_zero bound i.val)

/-- BOTH ORIGINAL exponents bound the COMPLETE actual finite mixed pair:
native line coefficients vanish above M, companion line coefficients above N. -/
theorem originalScheduledPrefix_mixed_private_lines_original_bounds (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    ∃ a b : Fin k → ℂ,
      T = (∑ i : Fin k, a i • originalScheduledPrivateLineSource bound i.val) +
        𝓕⁻ (∑ i : Fin k, b i • originalScheduledPrivateLineSource bound i.val) ∧
      (∀ i : Fin k, M < originalReflectedOrderSchedule bound i.val → a i = 0) ∧
      (∀ i : Fin k, N < originalReflectedOrderSchedule bound i.val → b i = 0) := by
  let ρ := originalScheduledPrefixRootSource bound k N T hF
  let Q := 𝓕 (T - ρ)
  obtain ⟨a, ha, _, haz⟩ := originalScheduledPrefixRootSource_private_lines_original_bound bound k M N T hT hF
  have hQ := originalScheduledPrefixRootSource_companion_fourier_both_strong bound k M N T hT hF
  obtain ⟨b, hb, _, hbz⟩ := originalScheduledPrefixRootSource_private_lines_original_bound bound k N M Q hQ.1 hQ.2
  have hself := originalScheduledPrefixRootSource_eq_self_onRoots bound k N M Q hQ.1 hQ.2
    (originalScheduledPrefixRootSource_complement_fourier_atomicOnRoots bound k N T hF)
  rw [hself] at hb
  have hc : T - ρ = 𝓕⁻ (∑ i : Fin k, b i • originalScheduledPrivateLineSource bound i.val) := by
    rw [← hb]
    exact (FourierTransform.fourierInv_fourier_eq (T - ρ)).symm
  refine ⟨a, b, ?_, haz, hbz⟩
  rw [← ha, ← hc]
  exact (add_sub_cancel _ _).symm

/-- COMPLETE original membership ALONE supplies its own finite original
exponents and the corresponding two literal order cutoffs on all mixed lines. -/
theorem originalScheduledPrefix_complete_mixed_private_lines_bounded (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    ∃ M N : ℕ, ∃ a b : Fin k → ℂ,
      T = (∑ i : Fin k, a i • originalScheduledPrivateLineSource bound i.val) +
        𝓕⁻ (∑ i : Fin k, b i • originalScheduledPrivateLineSource bound i.val) ∧
      (∀ i : Fin k, M < originalReflectedOrderSchedule bound i.val → a i = 0) ∧
      (∀ i : Fin k, N < originalReflectedOrderSchedule bound i.val → b i = 0) := by
  obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT.1
  obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hT.2
  exact ⟨M, N, originalScheduledPrefix_mixed_private_lines_original_bounds bound k M N T hM hN⟩

/-- The original exponent cutoffs give an ACTUAL index cutoff independent of
the finite prefix length: every mixed line after max M N vanishes internally. -/
theorem originalScheduledPrefix_mixed_private_lines_uniform_index_bound (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    ∃ a b : Fin k → ℂ,
      T = (∑ i : Fin k, a i • originalScheduledPrivateLineSource bound i.val) +
        𝓕⁻ (∑ i : Fin k, b i • originalScheduledPrivateLineSource bound i.val) ∧
      ∀ i : Fin k, max M N < i.val → a i = 0 ∧ b i = 0 := by
  obtain ⟨a, b, hab, ha, hb⟩ := originalScheduledPrefix_mixed_private_lines_original_bounds bound k M N T hT hF
  refine ⟨a, b, hab, ?_⟩
  intro i hi
  have horder : i.val ≤ originalReflectedOrderSchedule bound i.val :=
    (originalReflectedSchedule_spec bound i.val).2.2.2.1
  exact ⟨ha i ((lt_of_le_of_lt (le_max_left M N) hi).trans_le horder),
    hb i ((lt_of_le_of_lt (le_max_right M N) hi).trans_le horder)⟩

end
end MeyerGeneralProblem.StrongParity
