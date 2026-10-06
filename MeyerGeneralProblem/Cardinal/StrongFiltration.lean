module

public import MeyerGeneralProblem.Cardinal.MeyerTrichotomy

@[expose] public section

/-!
# The actual two-record strong-exponent filtration

These layers impose weighted absolute summability on both records of the
same distribution. They exhaust `StronglyTemperedMeyerSpace`, with a common
exponent obtained from the two separate exponents by taking their maximum.

Finite unbounded exponent layers suffice for countably infinite strong
Hamel rank. This is a construction criterion, not a constructed carrier.
No closed-Hilbert-layer or continuum conclusion is imported for these
weighted absolute-mass layers.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Both actual atomic records have summable weighted variation at `N`. -/
def StrongMeyerExponentLayer (S : LocallyFiniteCarrier) (N : ℕ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  stronglyTemperedAtomicAtExponent S N ⊓
    (stronglyTemperedAtomicAtExponent S N).comap temperedFourierLinearMap

@[simp]
theorem mem_strongMeyerExponentLayer_iff
    (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ) :
    T ∈ StrongMeyerExponentLayer S N ↔
      (HasLocallyAtomicAction S T ∧
        Summable (stronglyTemperedCoefficientTerm S N T)) ∧
      (HasLocallyAtomicAction S (FourierTransform.fourier T) ∧
        Summable (stronglyTemperedCoefficientTerm S N
          (FourierTransform.fourier T))) := Iff.rfl

theorem strongMeyerExponentLayer_mono (S : LocallyFiniteCarrier) :
    Monotone (StrongMeyerExponentLayer S) := by
  intro N M hNM T hT
  exact ⟨stronglyTemperedAtomicAtExponent_mono S hNM hT.1,
    stronglyTemperedAtomicAtExponent_mono S hNM hT.2⟩

theorem strongMeyerExponentLayer_le_strong (S : LocallyFiniteCarrier) (N : ℕ) :
    StrongMeyerExponentLayer S N ≤ StronglyTemperedMeyerSpace S := by
  intro T hT
  constructor
  · exact (mem_stronglyTemperedAtomicOnCarrier_iff S T).mpr ⟨N, hT.1⟩
  · exact (mem_stronglyTemperedAtomicOnCarrier_iff S
      (FourierTransform.fourier T)).mpr ⟨N, hT.2⟩

/-- Separate physical and spectral growth exponents can always be unified.
Both summability assertions concern the original isolation coefficients. -/
theorem mem_stronglyTemperedMeyerSpace_iff_exists_exponentLayer
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    T ∈ StronglyTemperedMeyerSpace S ↔
      ∃ N : ℕ, T ∈ StrongMeyerExponentLayer S N := by
  constructor
  · intro hT
    obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff S T).mp hT.1
    obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff S
      (FourierTransform.fourier T)).mp hT.2
    exact ⟨max N M,
      stronglyTemperedAtomicAtExponent_mono S (le_max_left N M) hN,
      stronglyTemperedAtomicAtExponent_mono S (le_max_right N M) hM⟩
  · rintro ⟨N, hN⟩
    exact strongMeyerExponentLayer_le_strong S N hN

/-- The exponent filtration is an exact algebraic exhaustion of the strong
space; it is not an exhaustion of the broad distributional space. -/
theorem iSup_strongMeyerExponentLayer_eq_strong (S : LocallyFiniteCarrier) :
    (⨆ N : ℕ, StrongMeyerExponentLayer S N) = StronglyTemperedMeyerSpace S := by
  apply le_antisymm
  · exact iSup_le (strongMeyerExponentLayer_le_strong S)
  · intro T hT
    obtain ⟨N, hN⟩ :=
      (mem_stronglyTemperedMeyerSpace_iff_exists_exponentLayer S T).mp hT
    exact (le_iSup (StrongMeyerExponentLayer S) N) hN

/-- A literal exponent-layer inclusion, with no distributional order shift. -/
def strongMeyerExponentLayerInclusion (S : LocallyFiniteCarrier) (N : ℕ) :
    StrongMeyerExponentLayer S N →ₗ[ℂ] StronglyTemperedMeyerSpace S :=
  Submodule.inclusion (strongMeyerExponentLayer_le_strong S N)

theorem strongMeyerExponentLayerInclusion_injective
    (S : LocallyFiniteCarrier) (N : ℕ) :
    Function.Injective (strongMeyerExponentLayerInclusion S N) :=
  Submodule.inclusion_injective _

theorem strongMeyerExponentLayerInclusion_cover (S : LocallyFiniteCarrier)
    (T : StronglyTemperedMeyerSpace S) :
    ∃ N : ℕ, ∃ U : StrongMeyerExponentLayer S N,
      strongMeyerExponentLayerInclusion S N U = T := by
  obtain ⟨N, hN⟩ :=
    (mem_stronglyTemperedMeyerSpace_iff_exists_exponentLayer S T).mp T.property
  exact ⟨N, ⟨T, hN⟩, rfl⟩

/-- Finite absolute-mass layers give an at-most-countable strong rank. -/
theorem strongMeyerRank_le_aleph0_of_finiteExponentLayers
    (S : LocallyFiniteCarrier)
    (hf : ∀ N : ℕ, FiniteDimensional ℂ (StrongMeyerExponentLayer S N)) :
    Module.rank ℂ (StronglyTemperedMeyerSpace S) ≤ Cardinal.aleph0 :=
  rank_le_aleph0_of_countable_finiteDimensional_cover
    (fun N => StrongMeyerExponentLayer S N) (strongMeyerExponentLayerInclusion S)
    hf (strongMeyerExponentLayerInclusion_cover S)

/-- The strong countable-cardinal gate: actual finite absolute-mass layers
with unbounded dimensions give exact countably infinite strong Hamel rank.
The carrier and these two analytic hypotheses still have to be constructed. -/
theorem strongMeyerRank_eq_aleph0_of_finiteUnboundedExponentLayers
    (S : LocallyFiniteCarrier)
    (hf : ∀ N : ℕ, FiniteDimensional ℂ (StrongMeyerExponentLayer S N))
    (hu : ∀ B : ℕ, ∃ N : ℕ,
      B < Module.finrank ℂ (StrongMeyerExponentLayer S N)) :
    Module.rank ℂ (StronglyTemperedMeyerSpace S) = Cardinal.aleph0 :=
  rank_eq_aleph0_of_countable_finiteDimensional_cover_unbounded
    (fun N => StrongMeyerExponentLayer S N) (strongMeyerExponentLayerInclusion S)
    (strongMeyerExponentLayerInclusion_injective S)
    hf (strongMeyerExponentLayerInclusion_cover S) hu

/-- Forgetting strong growth is an injection and only gives a rank upper
bound. Equality of broad and strong ranks does not follow. -/
theorem strongMeyerRank_le_distributionalMeyerRank (S : LocallyFiniteCarrier) :
    Module.rank ℂ (StronglyTemperedMeyerSpace S) ≤
      Module.rank ℂ (DistributionalMeyerSpace S) :=
  (Submodule.inclusion (stronglyTemperedMeyerSpace_le_distributionalMeyerSpace S)).rank_le_of_injective
    (Submodule.inclusion_injective _)

theorem strongMeyerRank_le_continuum (S : LocallyFiniteCarrier) :
    Module.rank ℂ (StronglyTemperedMeyerSpace S) ≤ Cardinal.mk ℂ :=
  (strongMeyerRank_le_distributionalMeyerRank S).trans
    ((rank_le_card ℂ (DistributionalMeyerSpace S)).trans
      (cardinalMk_distributionalMeyerSpace_le_complex S))

/-- Admission of every generator and exhaustion of every strong source
give equality with the finite algebraic span. Independent sources alone
do not give this exhaustion. -/
theorem strongGenerator_span_eq (S : LocallyFiniteCarrier)
    (g : ℕ → TemperedDistribution ℝ ℂ)
    (hg : ∀ n, g n ∈ StronglyTemperedMeyerSpace S)
    (hexhaust : ∀ T ∈ StronglyTemperedMeyerSpace S,
      T ∈ Submodule.span ℂ (Set.range g)) :
    Submodule.span ℂ (Set.range g) = StronglyTemperedMeyerSpace S := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact hg n
  · exact hexhaust

/-- The finite-synthesis interface for an actually admitted, independent,
exhaustive strong family. All three hypotheses remain explicit. -/
def strongGeneratorSynthesisEquiv (S : LocallyFiniteCarrier)
    (g : ℕ → TemperedDistribution ℝ ℂ)
    (hi : LinearIndependent ℂ g)
    (hg : ∀ n, g n ∈ StronglyTemperedMeyerSpace S)
    (hexhaust : ∀ T ∈ StronglyTemperedMeyerSpace S,
      T ∈ Submodule.span ℂ (Set.range g)) :
    (ℕ →₀ ℂ) ≃ₗ[ℂ] StronglyTemperedMeyerSpace S :=
  hi.linearCombinationEquiv.trans
    (LinearEquiv.ofEq _ _ (strongGenerator_span_eq S g hg hexhaust))

theorem strongGeneratorSynthesisEquiv_apply (S : LocallyFiniteCarrier)
    (g : ℕ → TemperedDistribution ℝ ℂ)
    (hi : LinearIndependent ℂ g)
    (hg : ∀ n, g n ∈ StronglyTemperedMeyerSpace S)
    (hexhaust : ∀ T ∈ StronglyTemperedMeyerSpace S,
      T ∈ Submodule.span ℂ (Set.range g)) (c : ℕ →₀ ℂ) :
    (strongGeneratorSynthesisEquiv S g hi hg hexhaust c :
      TemperedDistribution ℝ ℂ) = Finsupp.linearCombination ℂ g c := rfl

/-- The complete strong-space rank follows from literal finite synthesis,
once strong admission, independence and exhaustion have all been proved. -/
theorem strongMeyerRank_eq_aleph0_of_complete_generators
    (S : LocallyFiniteCarrier) (g : ℕ → TemperedDistribution ℝ ℂ)
    (hi : LinearIndependent ℂ g)
    (hg : ∀ n, g n ∈ StronglyTemperedMeyerSpace S)
    (hexhaust : ∀ T ∈ StronglyTemperedMeyerSpace S,
      T ∈ Submodule.span ℂ (Set.range g)) :
    Module.rank ℂ (StronglyTemperedMeyerSpace S) = Cardinal.aleph0 := by
  rw [← (strongGeneratorSynthesisEquiv S g hi hg hexhaust).rank_eq,
    rank_finsupp_self']
  exact Cardinal.mk_eq_aleph0 ℕ

end

end MeyerGeneralProblem
