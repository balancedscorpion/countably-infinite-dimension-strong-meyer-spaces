module

public import MeyerGeneralProblem.Cardinal.IntrinsicMeyerRank

@[expose] public section

/-!
# Carrier inclusion and transport of infinite Meyer layers

Enlarging the carrier enlarges both the distributional Meyer space and every
intrinsic fixed-order layer. This is the exact monotonicity needed after
density-preserving thinning; no new enumeration or bound on atomic masses is
introduced. Reduced endpoint radii are not asserted to be monotone.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Atomicity on a subcarrier implies atomicity on the larger carrier. -/
theorem AtomicOnCarrier.mono {S T : LocallyFiniteCarrier}
    (hST : S.carrier ⊆ T.carrier) {u : TemperedDistribution ℝ ℂ}
    (hu : AtomicOnCarrier S u) : AtomicOnCarrier T u := by
  intro f hf
  exact hu f (schwartzVanishingSubmodule_antitone hST hf)

/-- Local atomic action is monotone without total-variation growth conditions. -/
theorem HasLocallyAtomicAction.mono {S T : LocallyFiniteCarrier}
    (hST : S.carrier ⊆ T.carrier) {u : TemperedDistribution ℝ ℂ}
    (hu : HasLocallyAtomicAction S u) : HasLocallyAtomicAction T u :=
  atomicOnCarrier_hasLocallyAtomicAction T u
    ((hasLocallyAtomicAction_atomicOnCarrier S u hu).mono hST)

/-- Carrier inclusion induces actual inclusion of distributional Meyer spaces. -/
theorem distributionalMeyerSpace_mono {S T : LocallyFiniteCarrier}
    (hST : S.carrier ⊆ T.carrier) :
    DistributionalMeyerSpace S ≤ DistributionalMeyerSpace T := by
  intro u hu
  exact ⟨hu.1.mono hST, hu.2.mono hST⟩

/-- Carrier inclusion preserves an intrinsic physical-support vector at the
same Hermite order. -/
theorem fixedOrderPhysicalSupport_mono {S T : LocallyFiniteCarrier}
    (hST : S.carrier ⊆ T.carrier) (m : ℕ) (hm : 1 ≤ m) :
    fixedOrderPhysicalSupport S m hm ≤ fixedOrderPhysicalSupport T m hm := by
  intro u hu
  rw [fixedOrderPhysicalSupport,
    mem_locallyFiniteSupportedHermiteMeasureSubspace_iff] at hu ⊢
  intro v
  apply hu ⟨v, ?_⟩
  rw [mem_locallyFiniteCarrierHermiteVanishingSubspace_iff] at *
  intro x
  exact (mem_locallyFiniteCarrierHermiteVanishingSubspace_iff m hm T v).mp
    v.property ⟨x, hST x.property⟩

/-- Intrinsic Meyer layers are monotone in the carrier at the same order. -/
theorem fixedOrderMeyerLayer_carrier_mono {S T : LocallyFiniteCarrier}
    (hST : S.carrier ⊆ T.carrier) (m : ℕ) (hm : 1 ≤ m) :
    FixedOrderMeyerLayer S m hm ≤ FixedOrderMeyerLayer T m hm := by
  intro u hu
  rw [mem_fixedOrderMeyerLayer_iff] at hu ⊢
  exact ⟨fixedOrderPhysicalSupport_mono hST m hm hu.1,
    fixedOrderPhysicalSupport_mono hST m hm hu.2⟩

/-- An infinite layer of a subcarrier stays infinite after enlargement. -/
theorem infinite_fixedOrderMeyerLayer_mono {S T : LocallyFiniteCarrier}
    (hST : S.carrier ⊆ T.carrier) (m : ℕ) (hm : 1 ≤ m)
    (hinf : ¬ FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm)) :
    ¬ FiniteDimensional ℂ (FixedOrderMeyerLayer T m hm) := by
  intro hfinite
  let : FiniteDimensional ℂ (FixedOrderMeyerLayer T m hm) := hfinite
  let j := Submodule.inclusion (fixedOrderMeyerLayer_carrier_mono hST m hm)
  exact hinf (FiniteDimensional.of_injective j (Submodule.inclusion_injective _))

/-- A genuine supercritical certificate transports from a subcarrier without
changing its witnessing order. -/
def SupercriticalEndpointCertificate.of_subcarrier {S T : LocallyFiniteCarrier}
    (C : SupercriticalEndpointCertificate S) (hST : S.carrier ⊆ T.carrier) :
    SupercriticalEndpointCertificate T where
  order := C.order
  order_pos := C.order_pos
  infiniteLayer := infinite_fixedOrderMeyerLayer_mono hST C.order C.order_pos C.infiniteLayer

/-- The empty-carrier boundary: annihilating all Schwartz tests means zero. -/
theorem atomicOnCarrier_eq_zero_of_empty {S : LocallyFiniteCarrier}
    (hS : S.carrier = ∅) {u : TemperedDistribution ℝ ℂ}
    (hu : AtomicOnCarrier S u) : u = 0 := by
  ext f
  apply hu f
  intro x hx
  rw [hS] at hx
  exact False.elim hx

/-- The distributional Meyer space on an empty carrier is the zero space. -/
theorem distributionalMeyerSpace_eq_bot_of_empty {S : LocallyFiniteCarrier}
    (hS : S.carrier = ∅) : DistributionalMeyerSpace S = ⊥ := by
  apply bot_unique
  intro u hu
  exact atomicOnCarrier_eq_zero_of_empty hS
    (hasLocallyAtomicAction_atomicOnCarrier S u hu.1)

end

end MeyerGeneralProblem
