module

public import MeyerGeneralProblem.Cardinal.Strong.ArrayNumeratorUniqueness

@[expose] public section

/-! Finite numerators for arbitrary actual atomic Fourier pairs.
No constructed-image membership is required. -/

namespace MeyerGeneralProblem

noncomputable section

open Filter
open scoped SchwartzMap FourierTransform Topology

variable {G : Type*} [AddCommGroup G]

/-- Every nonzero finite annihilator has actual extremal frequencies. -/
theorem finiteAnnihilator_extrema (L : G →+ ℝ) (hL : Function.Injective L)
    (p : G →₀ ℂ) (hp : p ≠ 0) :
    ∃ m₀ m₁, p m₀ ≠ 0 ∧ p m₁ ≠ 0 ∧
      (∀ m ∈ p.support, L m₀ ≤ L m ∧ L m ≤ L m₁) ∧
      (∀ m ∈ p.support, m ≠ m₀ → L m₀ < L m) ∧
      (∀ m ∈ p.support, m ≠ m₁ → L m < L m₁) := by
  classical
  have hs : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  obtain ⟨m₀, hm₀, hlo⟩ := p.support.exists_min_image L hs
  obtain ⟨m₁, hm₁, hhi⟩ := p.support.exists_max_image L hs
  refine ⟨m₀, m₁, Finsupp.mem_support_iff.mp hm₀, Finsupp.mem_support_iff.mp hm₁,
    fun m hm => ⟨hlo m hm, hhi m hm⟩, ?_, ?_⟩
  · intro m hm hne
    exact lt_of_le_of_ne (hlo m hm) (fun h => hne (hL h.symm))
  · intro m hm hne
    exact lt_of_le_of_ne (hhi m hm) (fun h => hne (hL h))

/-- A finite actual numerator exists for each original supported Fourier pair,
at EVERY real cut, with its two original convolution formulas. -/
theorem originalFourierPair_exists_finite_numerator (L : G →+ ℝ)
    (hL : Function.Injective L) (p : G →₀ ℂ) (hp : p ≠ 0)
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier A T) (hFT : AtomicOnCarrier B (𝓕 T))
    (hz : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) (s : ℝ) :
    ∃ R : G →₀ ℂ, ∀ n,
      R n = annihilatorArrayConvolution p (arrayPositiveCut L s (originalFourierArray L B T)) n ∧
      R n = -annihilatorArrayConvolution p (arrayNegativeCut L s (originalFourierArray L B T)) n := by
  obtain ⟨m₀, m₁, _, _, hbounds, _, _⟩ := finiteAnnihilator_extrema L hL p hp
  have hu := originalFourierArray_frequencyLocallyFinite L hL B T
  have hc := originalFourierArray_annihilated L p A B T hT hFT hz
  refine ⟨finiteCutNumerator L p s (L m₀) (L m₁)
    (fun m hm => (hbounds m hm).1) (fun m hm => (hbounds m hm).2)
    _ hu hc, fun n => ⟨rfl, ?_⟩⟩
  exact cutArrayNumerator_eq_negative L p s _ hc n

/-- Original atomic distributions with identical canonical coefficients agree
on all Schwartz tests, using the actual compact approximation. -/
theorem atomic_eq_of_coefficients (S : LocallyFiniteCarrier)
    (T U : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T) (hU : AtomicOnCarrier S U)
    (hc : ∀ x : S.subtype, T (S.isolationSchwartz x) = U (S.isolationSchwartz x)) : T = U := by
  have hd : AtomicOnCarrier S (T - U) := by
    intro f hf
    change T f - U f = 0
    rw [hT f hf, hU f hf, sub_self]
  have hcompact (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f) : (T - U) f = 0 := by
    obtain ⟨E, _, hsum⟩ := atomicOnCarrier_isLocallyAtomicCoefficientFamily S (T - U) hd f hf
    rw [hsum]
    apply Finset.sum_eq_zero
    intro x _
    change (T (S.isolationSchwartz x) - U (S.isolationSchwartz x)) * f x = 0
    rw [hc x, sub_self, zero_mul]
  apply sub_eq_zero.mp
  ext f
  have ht := (T - U).continuous.tendsto f |>.comp (compactSchwartzApproximation_tendsto f)
  have hz : Tendsto (fun n => (T - U) (compactSchwartzApproximation n f)) atTop (𝓝 0) := by
    convert! (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)) using 1
    funext n
    exact hcompact _ (compactSchwartzApproximation_hasCompactSupport n f)
  exact tendsto_nhds_unique ht hz

/-- The full original Fourier array is faithful when the actual spectral
carrier lies in the injective frequency lattice. -/
theorem originalFourierArray_injective (L : G →+ ℝ) (B : LocallyFiniteCarrier)
    (hB : B.carrier ⊆ Set.range L) (T U : TemperedDistribution ℝ ℂ)
    (hFT : AtomicOnCarrier B (𝓕 T)) (hFU : AtomicOnCarrier B (𝓕 U))
    (heq : originalFourierArray L B T = originalFourierArray L B U) : T = U := by
  have hfourier : 𝓕 T = 𝓕 U := by
    apply atomic_eq_of_coefficients B _ _ hFT hFU
    intro x
    obtain ⟨n, hn⟩ := hB x.property
    have h := congrFun heq n
    have hnB : L n ∈ B.carrier := hn.symm ▸ x.property
    unfold originalFourierArray extendedAtomicCoefficient at h
    rw [dite_eq_left hnB, dite_eq_left hnB] at h
    simpa only [hn] using h
  simpa only [FourierTransform.fourierInv_fourier_eq] using congrArg FourierTransform.fourierInv hfourier

/-- The actual cut numerator is injective on the ENTIRE supported pair space,
not merely the forward constructed image. -/
theorem originalFourierPair_cutNumerator_injective (L : G →+ ℝ)
    (hL : Function.Injective L) (p : G →₀ ℂ) (hp : p ≠ 0)
    (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ Set.range L)
    (T U : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier A T) (hU : AtomicOnCarrier A U)
    (hFT : AtomicOnCarrier B (𝓕 T)) (hFU : AtomicOnCarrier B (𝓕 U))
    (hz : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) (s : ℝ)
    (heq : cutArrayNumerator L p s (originalFourierArray L B T) =
      cutArrayNumerator L p s (originalFourierArray L B U)) : T = U := by
  obtain ⟨m₀, m₁, hm₀, hm₁, _, hmin, hmax⟩ := finiteAnnihilator_extrema L hL p hp
  apply originalFourierArray_injective L B hB T U hFT hFU
  exact cutArrayNumerator_injective_on_kernel L p m₀ m₁ hm₀ hm₁ hmin hmax s _ _
    (originalFourierArray_frequencyLocallyFinite L hL B T)
    (originalFourierArray_frequencyLocallyFinite L hL B U)
    (originalFourierArray_annihilated L p A B T hT hFT hz)
    (originalFourierArray_annihilated L p A B U hU hFU hz) heq

end

end MeyerGeneralProblem
