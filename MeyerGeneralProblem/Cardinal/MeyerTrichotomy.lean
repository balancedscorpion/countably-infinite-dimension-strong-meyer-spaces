module

public import MeyerGeneralProblem.Cardinal.AtomicCoefficientBound
public import MeyerGeneralProblem.Cardinal.SeparableHilbertHamel
public import MeyerGeneralProblem.Distribution.SchwartzDefect
public import MeyerGeneralProblem.Hermite.Exhaustion

@[expose] public section

/-!
# Cardinal trichotomy through represented Hermite layers

The layers in this module are pullbacks of the genuine Schwartz-defect
annihilator through Hermite distribution realization.  They are closed
Hilbert subspaces and exhaust the distributional Meyer space.  They are
deliberately distinct from the intrinsic `FixedOrderMeyerLayer`: no
same-order intrinsic support identification is used here.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The closed order-`-m` represented Meyer layer.  Membership means that
the realized tempered distribution annihilates the genuine Schwartz defect.
This is not a definition of the intrinsic fixed-order support layer. -/
def RepresentedMeyerLayer (S : LocallyFiniteCarrier) (m : ℕ) :
    Submodule ℂ (HermiteScale (-(m : ℤ))) :=
  (schwartzAnnihilator (schwartzDefectSubmodule S)).comap
    (hermiteScaleDistributionCLM m).toLinearMap

@[simp]
theorem mem_representedMeyerLayer_iff
    (S : LocallyFiniteCarrier) (m : ℕ) (u : HermiteScale (-(m : ℤ))) :
    u ∈ RepresentedMeyerLayer S m ↔
      hermiteScaleDistribution m u ∈ DistributionalMeyerSpace S := by
  rw [distributionalMeyerSpace_eq_schwartzDefectAnnihilator]
  rfl

/-- Represented layers are closed in their Hermite Hilbert spaces. -/
theorem representedMeyerLayer_isClosed (S : LocallyFiniteCarrier) (m : ℕ) :
    IsClosed (RepresentedMeyerLayer S m : Set (HermiteScale (-(m : ℤ)))) := by
  have hset : (RepresentedMeyerLayer S m : Set (HermiteScale (-(m : ℤ)))) =
      ⋂ f ∈ schwartzDefectSubmodule S,
        {u | hermiteScaleDistribution m u f = 0} := by
    ext u
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [hset]
  apply isClosed_biInter
  intro f hf
  exact isClosed_eq
    (((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ f).continuous).comp
      (hermiteScaleDistributionCLM m).continuous) continuous_const

/-- The realization map from a represented layer into the distributional
Meyer space. -/
def representedMeyerLayerRealization (S : LocallyFiniteCarrier) (m : ℕ) :
    RepresentedMeyerLayer S m →ₗ[ℂ] DistributionalMeyerSpace S where
  toFun u := ⟨hermiteScaleDistribution m u,
    (mem_representedMeyerLayer_iff S m u).mp u.property⟩
  map_add' u v := by
    apply Subtype.ext
    exact (hermiteScaleDistributionCLM m).map_add u v
  map_smul' c u := by
    apply Subtype.ext
    exact (hermiteScaleDistributionCLM m).map_smul c u

@[simp]
theorem representedMeyerLayerRealization_apply
    (S : LocallyFiniteCarrier) (m : ℕ) (u : RepresentedMeyerLayer S m) :
    (representedMeyerLayerRealization S m u : TemperedDistribution ℝ ℂ) =
      hermiteScaleDistribution m u := rfl

theorem representedMeyerLayerRealization_injective
    (S : LocallyFiniteCarrier) (m : ℕ) :
    Function.Injective (representedMeyerLayerRealization S m) := by
  intro u v huv
  apply Subtype.ext
  apply hermiteScaleDistribution_injective m
  exact congrArg (fun T : DistributionalMeyerSpace S =>
    (T : TemperedDistribution ℝ ℂ)) huv

/-- Every distributional Meyer element occurs in a represented layer. -/
theorem exists_representedMeyerLayer_realization
    (S : LocallyFiniteCarrier) (T : DistributionalMeyerSpace S) :
    ∃ m : ℕ, ∃ u : RepresentedMeyerLayer S m,
      representedMeyerLayerRealization S m u = T := by
  obtain ⟨m, u, hu⟩ := exists_hermiteScale_representation
    (T : TemperedDistribution ℝ ℂ)
  have hmem : u ∈ RepresentedMeyerLayer S m := by
    rw [mem_representedMeyerLayer_iff, hu]
    exact T.property
  refine ⟨m, ⟨u, hmem⟩, ?_⟩
  exact Subtype.ext hu

/-- Adjacent scale inclusion preserves represented Meyer membership. -/
theorem hermiteScaleInclusion_mem_representedMeyerLayer
    (S : LocallyFiniteCarrier) (m : ℕ) (u : HermiteScale (-(m : ℤ)))
    (hu : u ∈ RepresentedMeyerLayer S m) :
    hermiteScaleInclusion m u ∈ RepresentedMeyerLayer S (m + 1) := by
  rw [mem_representedMeyerLayer_iff, hermiteScaleDistribution_inclusion]
  exact (mem_representedMeyerLayer_iff S m u).mp hu

/-- The image of one represented Hermite layer inside the distributional
Meyer space. -/
def representedMeyerRange (S : LocallyFiniteCarrier) (m : ℕ) :
    Submodule ℂ (DistributionalMeyerSpace S) :=
  (representedMeyerLayerRealization S m).range

theorem representedMeyerRange_mono (S : LocallyFiniteCarrier) :
    Monotone (representedMeyerRange S) := by
  apply monotone_nat_of_le_succ
  intro m T hT
  obtain ⟨u, rfl⟩ := hT
  refine ⟨⟨hermiteScaleInclusion m u,
    hermiteScaleInclusion_mem_representedMeyerLayer S m u u.property⟩, ?_⟩
  apply Subtype.ext
  exact hermiteScaleDistribution_inclusion m u

/-- The increasing represented ranges exhaust the distributional Meyer
space as an algebraic union. -/
theorem iSup_representedMeyerRange_eq_top (S : LocallyFiniteCarrier) :
    (⨆ m : ℕ, representedMeyerRange S m) = ⊤ := by
  apply top_unique
  intro T hT
  obtain ⟨m, u, hu⟩ := exists_representedMeyerLayer_realization S T
  exact (le_iSup (representedMeyerRange S) m) ⟨u, hu⟩

/-- An algebraic vector space covered by countably many finite-dimensional
linear images has at most countable Hamel rank.  This lemma is independent
of the topology and of the represented-layer construction. -/
theorem rank_le_aleph0_of_countable_finiteDimensional_cover
    {E : Type} [AddCommGroup E] [Module ℂ E]
    (H : ℕ → Type) [∀ m, AddCommGroup (H m)] [∀ m, Module ℂ (H m)]
    (L : ∀ m, H m →ₗ[ℂ] E)
    (hfinite : ∀ m, FiniteDimensional ℂ (H m))
    (hcover : ∀ x : E, ∃ m, ∃ u : H m, L m u = x) :
    Module.rank ℂ E ≤ Cardinal.aleph0 := by
  let : ∀ m, FiniteDimensional ℂ (H m) := hfinite
  let b : ∀ m, Module.Basis (Fin (Module.finrank ℂ (H m))) ℂ (H m) :=
    fun m => Module.finBasis ℂ (H m)
  let I : Type := Σ m : ℕ, Fin (Module.finrank ℂ (H m))
  let g : I → E := fun i => L i.1 (b i.1 i.2)
  have hspan : Submodule.span ℂ (Set.range g) = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨m, u, rfl⟩ := hcover x
    rw [← (b m).sum_repr u, map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨m, i⟩, rfl⟩
  have hcard : Cardinal.mk (Set.range g) ≤ Cardinal.aleph0 :=
    Cardinal.mk_range_le.trans (Cardinal.mk_le_aleph0 (α := I))
  have h := (rank_span_le (R := ℂ) (Set.range g)).trans hcard
  rwa [hspan, rank_top] at h

/-- A monotone exhaustive sequence of finite-dimensional subspaces with
bounded dimensions stabilizes at the whole vector space. -/
theorem exists_eq_top_of_monotone_finiteDimensional_cover_bounded
    {E : Type} [AddCommGroup E] [Module ℂ E]
    (V : ℕ → Submodule ℂ E) (hmono : Monotone V)
    (hfinite : ∀ m, FiniteDimensional ℂ (V m))
    (hcover : ∀ x : E, ∃ m, x ∈ V m)
    (hbounded : ∃ B : ℕ, ∀ m, Module.finrank ℂ (V m) ≤ B) :
    ∃ m : ℕ, V m = ⊤ := by
  classical
  let : ∀ m, FiniteDimensional ℂ (V m) := hfinite
  let d : ℕ → ℕ := fun m => Module.finrank ℂ (V m)
  have hbdd : BddAbove (Set.range d) := by
    obtain ⟨B, hB⟩ := hbounded
    refine ⟨B, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact hB m
  have hfin : (Set.range d).Finite := hbdd.finite
  obtain ⟨D, hD, hmax⟩ := hfin.toFinset.exists_max_image id
    (⟨d 0, by simp⟩ : hfin.toFinset.Nonempty)
  obtain ⟨m, hm⟩ : ∃ m, d m = D := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_range] using hD
  have hmaxdim : ∀ n, d n ≤ d m := by
    intro n
    rw [hm]
    exact hmax (d n) (by simp)
  have hle : ∀ n, V n ≤ V m := by
    intro n
    have heq : V m = V (max n m) :=
      Submodule.eq_of_le_of_finrank_le (hmono (le_max_right n m))
        (hmaxdim (max n m))
    rw [heq]
    exact hmono (le_max_left n m)
  refine ⟨m, top_unique ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := hcover x
  exact hle n hn

/-- Countably many finite-dimensional injective linear layers with
unbounded dimensions have countably infinite total Hamel rank. -/
theorem rank_eq_aleph0_of_countable_finiteDimensional_cover_unbounded
    {E : Type} [AddCommGroup E] [Module ℂ E]
    (H : ℕ → Type) [∀ m, AddCommGroup (H m)] [∀ m, Module ℂ (H m)]
    (L : ∀ m, H m →ₗ[ℂ] E)
    (hinj : ∀ m, Function.Injective (L m))
    (hfinite : ∀ m, FiniteDimensional ℂ (H m))
    (hcover : ∀ x : E, ∃ m, ∃ u : H m, L m u = x)
    (hunbounded : ∀ B : ℕ, ∃ m, B < Module.finrank ℂ (H m)) :
    Module.rank ℂ E = Cardinal.aleph0 := by
  apply le_antisymm
  · exact rank_le_aleph0_of_countable_finiteDimensional_cover H L hfinite hcover
  · by_contra h
    have hsmall : Module.rank ℂ E < Cardinal.aleph0 := lt_of_not_ge h
    let : FiniteDimensional ℂ E := Module.rank_lt_aleph0_iff.mp hsmall
    obtain ⟨m, hm⟩ := hunbounded (Module.finrank ℂ E)
    have hdim := LinearMap.finrank_le_finrank_of_injective (hinj m)
    exact (not_lt_of_ge hdim) hm

/-- If every represented layer is finite-dimensional, the distributional
Meyer space has at most countable Hamel rank. -/
theorem distributionalMeyerSpace_rank_le_aleph0_of_finiteRepresentedLayers
    (S : LocallyFiniteCarrier)
    (hfinite : ∀ m : ℕ, FiniteDimensional ℂ (RepresentedMeyerLayer S m)) :
    Module.rank ℂ (DistributionalMeyerSpace S) ≤ Cardinal.aleph0 := by
  exact rank_le_aleph0_of_countable_finiteDimensional_cover
    (fun m => RepresentedMeyerLayer S m) (representedMeyerLayerRealization S)
    hfinite (exists_representedMeyerLayer_realization S)

/-- Uniformly bounded finite represented-layer dimensions force a finite
Hamel rank of the distributional Meyer space. -/
theorem distributionalMeyerSpace_rank_eq_finite_of_boundedFiniteRepresentedLayers
    (S : LocallyFiniteCarrier)
    (hfinite : ∀ m : ℕ, FiniteDimensional ℂ (RepresentedMeyerLayer S m))
    (hbounded : ∃ B : ℕ, ∀ m,
      Module.finrank ℂ (RepresentedMeyerLayer S m) ≤ B) :
    ∃ d : ℕ, Module.rank ℂ (DistributionalMeyerSpace S) = d := by
  let : ∀ m, FiniteDimensional ℂ (RepresentedMeyerLayer S m) := hfinite
  have hrangefinite : ∀ m, FiniteDimensional ℂ (representedMeyerRange S m) := by
    intro m
    exact LinearMap.finiteDimensional_range (representedMeyerLayerRealization S m)
  have hrangecover : ∀ T : DistributionalMeyerSpace S,
      ∃ m, T ∈ representedMeyerRange S m := by
    intro T
    obtain ⟨m, u, hu⟩ := exists_representedMeyerLayer_realization S T
    exact ⟨m, u, hu⟩
  have hrangebound : ∃ B : ℕ, ∀ m,
      Module.finrank ℂ (representedMeyerRange S m) ≤ B := by
    obtain ⟨B, hB⟩ := hbounded
    refine ⟨B, fun m => ?_⟩
    exact (LinearMap.finrank_range_le (representedMeyerLayerRealization S m)).trans (hB m)
  obtain ⟨m, hm⟩ := exists_eq_top_of_monotone_finiteDimensional_cover_bounded
    (representedMeyerRange S) (representedMeyerRange_mono S)
    hrangefinite hrangecover hrangebound
  let : FiniteDimensional ℂ (representedMeyerRange S m) := hrangefinite m
  have hsurj : Function.Surjective (representedMeyerRange S m).subtype := by
    intro T
    refine ⟨⟨T, ?_⟩, rfl⟩
    rw [hm]
    trivial
  let : FiniteDimensional ℂ (DistributionalMeyerSpace S) :=
    FiniteDimensional.of_surjective (representedMeyerRange S m).subtype hsurj
  exact ⟨Module.finrank ℂ (DistributionalMeyerSpace S),
    (Module.finrank_eq_rank ℂ (DistributionalMeyerSpace S)).symm⟩

/-- Finite represented layers with unbounded dimensions give countably
infinite Hamel rank. -/
theorem distributionalMeyerSpace_rank_eq_aleph0_of_finiteUnboundedRepresentedLayers
    (S : LocallyFiniteCarrier)
    (hfinite : ∀ m : ℕ, FiniteDimensional ℂ (RepresentedMeyerLayer S m))
    (hunbounded : ∀ B : ℕ, ∃ m,
      B < Module.finrank ℂ (RepresentedMeyerLayer S m)) :
    Module.rank ℂ (DistributionalMeyerSpace S) = Cardinal.aleph0 := by
  exact rank_eq_aleph0_of_countable_finiteDimensional_cover_unbounded
    (fun m => RepresentedMeyerLayer S m) (representedMeyerLayerRealization S)
    (representedMeyerLayerRealization_injective S) hfinite
    (exists_representedMeyerLayer_realization S) hunbounded

/-- One infinite-dimensional represented Hilbert layer forces continuum
Hamel rank of the full distributional Meyer space. -/
theorem distributionalMeyerSpace_rank_eq_continuum_of_infiniteRepresentedLayer
    (S : LocallyFiniteCarrier) (m : ℕ)
    (hinfinite : ¬ FiniteDimensional ℂ (RepresentedMeyerLayer S m)) :
    Module.rank ℂ (DistributionalMeyerSpace S) = Cardinal.mk ℂ := by
  let : CompleteSpace (RepresentedMeyerLayer S m) :=
    (representedMeyerLayer_isClosed S m).completeSpace_coe
  apply le_antisymm
  · exact (rank_le_card ℂ (DistributionalMeyerSpace S)).trans
      (cardinalMk_distributionalMeyerSpace_le_complex S)
  · exact (complex_le_rank_of_infiniteDimensional_complexHilbert hinfinite).trans
      ((representedMeyerLayerRealization S m).rank_le_of_injective
        (representedMeyerLayerRealization_injective S m))

/-- The distributional Meyer space has finite, countably infinite, or
continuum Hamel rank.  This unconditional result uses closed represented
Hermite layers and does not identify them with intrinsic fixed-order layers.
-/
theorem distributionalMeyerSpace_rank_trichotomy (S : LocallyFiniteCarrier) :
    let κ := Module.rank ℂ (DistributionalMeyerSpace S)
    κ < Cardinal.aleph0 ∨
      κ = Cardinal.aleph0 ∨
      κ = Cardinal.mk ℂ := by
  classical
  dsimp only
  by_cases hfinite : ∀ m : ℕ, FiniteDimensional ℂ (RepresentedMeyerLayer S m)
  · rcases lt_or_eq_of_le
      (distributionalMeyerSpace_rank_le_aleph0_of_finiteRepresentedLayers S hfinite) with
      hlt | heq
    · exact Or.inl hlt
    · exact Or.inr (Or.inl heq)
  · push Not at hfinite
    obtain ⟨m, hm⟩ := hfinite
    exact Or.inr (Or.inr
      (distributionalMeyerSpace_rank_eq_continuum_of_infiniteRepresentedLayer S m hm))

end

end MeyerGeneralProblem
