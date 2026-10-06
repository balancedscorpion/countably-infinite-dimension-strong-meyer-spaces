module

public import MeyerGeneralProblem.Distribution.OriginalStrongWeightedDualPair

@[expose] public section

/-! Closed, value-only carrier constraints on the genuine weighted C0 Fourier
pair. Both original atomic records satisfy these constraints internally. A dual
limit in this set has BOTH whole value-only atomic distributions. Recovery of
finite original weighted variation from its dual norm remains separate. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty FourierTransform

/-- BOTH C0 records annihilate the entire value vanishing ideal of the actual carrier. -/
def originalWeightedDualCarrierConstraints (S : LocallyFiniteCarrier) :
    Set (WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) :=
  {q | ∀ g : C₀(ℝ, ℂ), (∀ x : S.subtype, g x = 0) →
    q (g, 0) = 0 ∧ q (0, g) = 0}

/-- BOTH full value-only carrier constraints are weak-star closed. -/
theorem originalWeightedDualCarrierConstraints_isClosed (S : LocallyFiniteCarrier) :
    IsClosed (originalWeightedDualCarrierConstraints S) := by
  have he : originalWeightedDualCarrierConstraints S =
      ⋂ g : C₀(ℝ, ℂ), ⋂ (_ : ∀ x : S.subtype, g x = 0),
        {q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) | q (g, 0) = 0 ∧ q (0, g) = 0} := by
    ext q
    simp only [originalWeightedDualCarrierConstraints, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  apply isClosed_iInter
  intro g
  apply isClosed_iInter
  intro hg
  exact (isClosed_eq (WeakDual.eval_continuous (g, 0)) continuous_const).inter
    (isClosed_eq (WeakDual.eval_continuous (0, g)) continuous_const)

/-- The actual original weighted atomic dual annihilates EVERY C0 function vanishing on its carrier. -/
theorem originalStrongAtomicC0Dual_zero_of_vanishes (S : LocallyFiniteCarrier) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (g : C₀(ℝ, ℂ)) (hg : ∀ x : S.subtype, g x = 0) :
    originalStrongAtomicC0Dual S N T hT g = 0 := by
  change (∑' x : S.subtype, originalWeightedC0Coefficient S
    (fun y => T (S.isolationSchwartz y)) N x * g x) = 0
  simp only [hg, mul_zero, tsum_zero]

/-- BOTH actual original records satisfy the full closed carrier constraints internally. -/
theorem originalStrongPairC0Dual_carrierConstraints (S : LocallyFiniteCarrier) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) :
    (originalStrongPairC0Dual S N T hT hF).toWeakDual ∈ originalWeightedDualCarrierConstraints S := by
  intro g hg
  simp only [StrongDual.toWeakDual_apply, originalStrongPairC0Dual_apply, map_zero,
    add_zero, zero_add]
  exact ⟨originalStrongAtomicC0Dual_zero_of_vanishes S N T hT g hg,
    originalStrongAtomicC0Dual_zero_of_vanishes S N (𝓕 T) hF g hg⟩

/-- BOTH whole distributions of a support-constrained dual have value-only atomic action on the carrier. -/
theorem originalWeightedDualCarrierConstraints_atomic (S : LocallyFiniteCarrier) (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (hq : q ∈ originalWeightedDualCarrierConstraints S) :
    AtomicOnCarrier S (originalWeightedDualPhysicalDistribution N q) ∧
      AtomicOnCarrier S (originalWeightedDualSpectralDistribution N q) := by
  have hv (f : SchwartzMap ℝ ℂ) (hf : SchwartzVanishesOn S f) :
      ∀ x : S.subtype, originalWeightedSchwartzC0 N f x = 0 := by
    intro x
    rw [originalWeightedSchwartzC0_apply, hf x x.property, smul_zero]
  constructor
  · intro f hf
    exact (hq (originalWeightedSchwartzC0 N f) (hv f hf)).1
  · intro f hf
    exact (hq (originalWeightedSchwartzC0 N f) (hv f hf)).2

/-- The genuine weighted Fourier unit ball with BOTH full value-only carrier constraints.
Its identification with the original weighted-variation unit ball is not assumed. -/
def originalWeightedDualSupportedFourierPairBall (S : LocallyFiniteCarrier) (N : ℕ) :
    Set (WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) :=
  originalWeightedDualFourierPairBall N ∩ originalWeightedDualCarrierConstraints S

/-- The ACTUAL support-constrained weighted dual Fourier pair unit ball is compact. -/
theorem originalWeightedDualSupportedFourierPairBall_isCompact (S : LocallyFiniteCarrier) (N : ℕ) :
    IsCompact (originalWeightedDualSupportedFourierPairBall S N) :=
  (originalWeightedDualFourierPairBall_isCompact N).inter_right
    (originalWeightedDualCarrierConstraints_isClosed S)

/-- Every original same-N unit-variation Fourier pair enters the genuine compact carrier ball internally. -/
theorem originalStrongPairC0Dual_mem_supported_ball (S : LocallyFiniteCarrier) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) (hunit : originalStrongPairVariation S N T ≤ 1) :
    (originalStrongPairC0Dual S N T hT hF).toWeakDual ∈ originalWeightedDualSupportedFourierPairBall S N :=
  ⟨originalStrongPairC0Dual_mem_ball S N T hT hF hunit,
    originalStrongPairC0Dual_carrierConstraints S N T hT hF⟩

/-- BOTH ORIGINAL records and their original unit-variation bound ALONE recover the
WHOLE original Fourier pair inside the ACTUAL compact support-constrained dual ball. -/
theorem originalStrongPair_exists_weighted_dual_supported_ball (S : LocallyFiniteCarrier) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) (hunit : originalStrongPairVariation S N T ≤ 1) :
    ∃ q ∈ originalWeightedDualSupportedFourierPairBall S N,
      originalWeightedDualPhysicalDistribution N q = T ∧ originalWeightedDualSpectralDistribution N q = 𝓕 T :=
  ⟨_, originalStrongPairC0Dual_mem_supported_ball S N T hT hF hunit,
    originalStrongPairC0Dual_physical S N T hT hF, originalStrongPairC0Dual_spectral S N T hT hF⟩

/-- EVERY member of the actual compact carrier ball gives BOTH atomic records
and the genuine Fourier equation, without original-variation recovery being presumed. -/
theorem originalWeightedDualSupportedFourierPairBall_atomic_fourier (S : LocallyFiniteCarrier) (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (hq : q ∈ originalWeightedDualSupportedFourierPairBall S N) :
    AtomicOnCarrier S (originalWeightedDualPhysicalDistribution N q) ∧
      AtomicOnCarrier S (𝓕 (originalWeightedDualPhysicalDistribution N q)) := by
  have ha := originalWeightedDualCarrierConstraints_atomic S N q hq.2
  exact ⟨ha.1, hq.1.2 ▸ ha.2⟩

end
end MeyerGeneralProblem
