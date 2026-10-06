module

public import MeyerGeneralProblem.Cardinal.MeyerTrichotomy
public import MeyerGeneralProblem.Endpoint.Certificates
public import MeyerGeneralProblem.Hermite.DistributionCoherence

@[expose] public section

/-!
# Cardinal branches from the intrinsic fixed-order Meyer layers

The intrinsic layer realizations are injective, coherent with Hermite-scale
inclusion, and exhaustive at some positive order.  Their dimensions therefore
determine the total Hamel rank in the finite/bounded, finite/unbounded, and
infinite-layer cases.  Exhaustion may increase the Hermite order; no
same-order converse to intrinsic physical support is used.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The intrinsic Meyer intersection is a closed Hilbert subspace. -/
theorem fixedOrderMeyerLayer_isClosed
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    IsClosed (FixedOrderMeyerLayer S m hm : Set (HermiteScale (-(m : ℤ)))) := by
  change IsClosed
    ((fixedOrderPhysicalSupport S m hm : Set (HermiteScale (-(m : ℤ)))) ∩
      (fixedOrderInverseFourierSupport S m hm : Set (HermiteScale (-(m : ℤ)))))
  exact (fixedOrderPhysicalSupport S m hm).isClosed'.inter
    (fixedOrderInverseFourierSupport S m hm).isClosed'

/-- Finite-dimensional intrinsic layers have monotone natural dimensions. -/
theorem fixedOrderFinrank_mono
    (S : LocallyFiniteCarrier) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hfinite_m : FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm))
    (hfinite_n : FiniteDimensional ℂ (FixedOrderMeyerLayer S n (hm.trans hmn))) :
    Module.finrank ℂ (FixedOrderMeyerLayer S m hm) ≤
      Module.finrank ℂ (FixedOrderMeyerLayer S n (hm.trans hmn)) := by
  let : FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm) := hfinite_m
  let : FiniteDimensional ℂ (FixedOrderMeyerLayer S n (hm.trans hmn)) := hfinite_n
  have h := fixedOrderRank_mono S hm hmn
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h
  exact_mod_cast h

/-- The image of the positive order `m + 1` intrinsic layer in the full
distributional Meyer space. -/
def intrinsicMeyerRange (S : LocallyFiniteCarrier) (m : ℕ) :
    Submodule ℂ (DistributionalMeyerSpace S) :=
  (fixedOrderMeyerLayerToDistributionalMeyerSpace S (m + 1) (by omega)).toLinearMap.range

/-- Coherent realization turns positive intrinsic layers into an increasing
sequence of subspaces of a single vector space. -/
theorem intrinsicMeyerRange_mono (S : LocallyFiniteCarrier) :
    Monotone (intrinsicMeyerRange S) := by
  apply monotone_nat_of_le_succ
  intro m T hT
  obtain ⟨u, rfl⟩ := hT
  refine ⟨fixedOrderMeyerLayerInclusion S (m + 1) (by omega) u, ?_⟩
  apply Subtype.ext
  exact hermiteScaleDistribution_inclusion (m + 1) u

/-- Every distributional Meyer vector lies in one positive intrinsic range. -/
theorem exists_mem_intrinsicMeyerRange
    (S : LocallyFiniteCarrier) (T : DistributionalMeyerSpace S) :
    ∃ m : ℕ, T ∈ intrinsicMeyerRange S m := by
  obtain ⟨m, u, hu⟩ := fixedOrderMeyerLayerToDistributionalMeyerSpace_cover S T
  exact ⟨m, u, hu⟩

/-- The positive intrinsic ranges exhaust the distributional Meyer space. -/
theorem iSup_intrinsicMeyerRange_eq_top (S : LocallyFiniteCarrier) :
    (⨆ m : ℕ, intrinsicMeyerRange S m) = ⊤ := by
  apply top_unique
  intro T hT
  obtain ⟨m, hm⟩ := exists_mem_intrinsicMeyerRange S T
  exact (le_iSup (intrinsicMeyerRange S) m) hm

/-- If every positive intrinsic layer is finite-dimensional, the total
Hamel rank is at most countable. -/
theorem meyerRank_le_aleph0_of_finiteLayers
    (S : LocallyFiniteCarrier)
    (hfinite : ∀ m : ℕ, ∀ hm : 1 ≤ m,
      FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm)) :
    Module.rank ℂ (DistributionalMeyerSpace S) ≤ Cardinal.aleph0 := by
  exact rank_le_aleph0_of_countable_finiteDimensional_cover
    (fun m => FixedOrderMeyerLayer S (m + 1) (by omega))
    (fun m => (fixedOrderMeyerLayerToDistributionalMeyerSpace
      S (m + 1) (by omega)).toLinearMap)
    (fun m => hfinite (m + 1) (by omega))
    (fixedOrderMeyerLayerToDistributionalMeyerSpace_cover S)

/-- Uniformly bounded finite positive intrinsic layers force finite total
Hamel rank.  The bound concerns the actual intrinsic layer dimensions. -/
theorem meyerRank_eq_finite_of_uniformlyBoundedFiniteLayers
    (S : LocallyFiniteCarrier)
    (hfinite : ∀ m : ℕ, ∀ hm : 1 ≤ m,
      FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm))
    (hbounded : ∃ B : ℕ, ∀ m : ℕ, ∀ hm : 1 ≤ m,
      Module.finrank ℂ (FixedOrderMeyerLayer S m hm) ≤ B) :
    ∃ d : ℕ, Module.rank ℂ (DistributionalMeyerSpace S) = d := by
  let : ∀ m : ℕ, ∀ hm : 1 ≤ m,
      FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm) := hfinite
  have hrangefinite : ∀ m, FiniteDimensional ℂ (intrinsicMeyerRange S m) := by
    intro m
    exact LinearMap.finiteDimensional_range
      (fixedOrderMeyerLayerToDistributionalMeyerSpace S (m + 1) (by omega)).toLinearMap
  have hrangebound : ∃ B : ℕ, ∀ m,
      Module.finrank ℂ (intrinsicMeyerRange S m) ≤ B := by
    obtain ⟨B, hB⟩ := hbounded
    refine ⟨B, fun m => ?_⟩
    exact (LinearMap.finrank_range_le
      (fixedOrderMeyerLayerToDistributionalMeyerSpace S (m + 1) (by omega)).toLinearMap).trans
      (hB (m + 1) (by omega))
  obtain ⟨m, hm⟩ := exists_eq_top_of_monotone_finiteDimensional_cover_bounded
    (intrinsicMeyerRange S) (intrinsicMeyerRange_mono S) hrangefinite
    (exists_mem_intrinsicMeyerRange S) hrangebound
  let : FiniteDimensional ℂ (intrinsicMeyerRange S m) := hrangefinite m
  have hsurj : Function.Surjective (intrinsicMeyerRange S m).subtype := by
    intro T
    refine ⟨⟨T, ?_⟩, rfl⟩
    rw [hm]
    trivial
  let : FiniteDimensional ℂ (DistributionalMeyerSpace S) :=
    FiniteDimensional.of_surjective (intrinsicMeyerRange S m).subtype hsurj
  exact ⟨Module.finrank ℂ (DistributionalMeyerSpace S),
    (Module.finrank_eq_rank ℂ (DistributionalMeyerSpace S)).symm⟩

/-- Finite positive intrinsic layers with unbounded dimensions give exactly
countably infinite total Hamel rank. -/
theorem meyerRank_eq_aleph0_of_finiteUnboundedLayers
    (S : LocallyFiniteCarrier)
    (hfinite : ∀ m : ℕ, ∀ hm : 1 ≤ m,
      FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm))
    (hunbounded : ∀ B : ℕ, ∃ m : ℕ, ∃ hm : 1 ≤ m,
      B < Module.finrank ℂ (FixedOrderMeyerLayer S m hm)) :
    Module.rank ℂ (DistributionalMeyerSpace S) = Cardinal.aleph0 := by
  apply rank_eq_aleph0_of_countable_finiteDimensional_cover_unbounded
    (fun m => FixedOrderMeyerLayer S (m + 1) (by omega))
    (fun m => (fixedOrderMeyerLayerToDistributionalMeyerSpace
      S (m + 1) (by omega)).toLinearMap)
    (fun m => fixedOrderMeyerLayerToDistributionalMeyerSpace_injective
      S (m + 1) (by omega))
    (fun m => hfinite (m + 1) (by omega))
    (fixedOrderMeyerLayerToDistributionalMeyerSpace_cover S)
  intro B
  obtain ⟨m, hm, hB⟩ := hunbounded B
  refine ⟨m, hB.trans_le ?_⟩
  exact fixedOrderFinrank_mono S hm (Nat.le_succ m)
    (hfinite m hm) (hfinite (m + 1) (by omega))

/-- One infinite positive intrinsic Hilbert layer forces continuum total
Hamel rank. -/
theorem meyerRank_eq_continuum_of_infiniteLayer
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (hinfinite : ¬ FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm)) :
    Module.rank ℂ (DistributionalMeyerSpace S) = Cardinal.mk ℂ := by
  let : CompleteSpace (FixedOrderMeyerLayer S m hm) :=
    (fixedOrderMeyerLayer_isClosed S m hm).completeSpace_coe
  apply le_antisymm
  · exact (rank_le_card ℂ (DistributionalMeyerSpace S)).trans
      (cardinalMk_distributionalMeyerSpace_le_complex S)
  · exact (complex_le_rank_of_infiniteDimensional_complexHilbert hinfinite).trans
      ((fixedOrderMeyerLayerToDistributionalMeyerSpace S m hm).toLinearMap.rank_le_of_injective
        (fixedOrderMeyerLayerToDistributionalMeyerSpace_injective S m hm))

/-- A subcritical certificate gives at most countable total rank; it does
not assert that the total rank is finite. -/
theorem SubcriticalEndpointCertificate.rank_le_aleph0
    {S : LocallyFiniteCarrier} (C : SubcriticalEndpointCertificate S) :
    Module.rank ℂ (DistributionalMeyerSpace S) ≤ Cardinal.aleph0 :=
  meyerRank_le_aleph0_of_finiteLayers S C.finiteLayer

/-- A subcritical certificate rules out continuum total Hamel rank. -/
theorem SubcriticalEndpointCertificate.rank_ne_continuum
    {S : LocallyFiniteCarrier} (C : SubcriticalEndpointCertificate S) :
    Module.rank ℂ (DistributionalMeyerSpace S) ≠ Cardinal.mk ℂ := by
  apply ne_of_lt
  apply C.rank_le_aleph0.trans_lt
  rw [Cardinal.mk_complex]
  exact Cardinal.aleph0_lt_continuum

/-- A supercritical certificate forces continuum total Hamel rank. -/
theorem SupercriticalEndpointCertificate.rank_eq_continuum
    {S : LocallyFiniteCarrier} (C : SupercriticalEndpointCertificate S) :
    Module.rank ℂ (DistributionalMeyerSpace S) = Cardinal.mk ℂ :=
  meyerRank_eq_continuum_of_infiniteLayer S C.order C.order_pos C.infiniteLayer

end

end MeyerGeneralProblem
