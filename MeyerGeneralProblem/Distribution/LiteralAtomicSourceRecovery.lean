module

public import MeyerGeneralProblem.Distribution.OriginalWeightedAtomicRestriction
public import MeyerGeneralProblem.Cardinal.Strong.OriginalPairNumerator

@[expose] public section

/-! Once a GENUINE disjoint-support decomposition has been recovered, its
pieces are the literal restrictions of the original record. Common-carrier
isolation tests prove this as equality of whole distributions. -/
namespace MeyerGeneralProblem
noncomputable section

/-- Isolation on a larger actual carrier gives the ORIGINAL zero-extended
coefficient at every larger-carrier point, including points outside the source. -/
theorem atomic_isolation_apply_on_larger_carrier (S U : LocallyFiniteCarrier)
    (hSU : S.carrier ⊆ U.carrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T) (x : U.subtype) :
    T (U.isolationSchwartz x) = extendedAtomicCoefficient S T x := by
  rw [atomic_action_singleton_values S T hT _ x]
  · rw [U.isolationSchwartz_self, mul_one]
  · intro y hy hyx
    exact U.isolationSchwartz_of_mem_of_ne x (hSU hy) hyx

/-- If a genuine distribution is atomic on TWO carriers, every ORIGINAL
coefficient at a point of one carrier outside the other is zero. -/
theorem atomic_isolation_eq_zero_off_other_carrier (A B : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B T)
    (x : A.subtype) (hx : (x : ℝ) ∉ B.carrier) : T (A.isolationSchwartz x) = 0 := by
  let U := A.union B
  have hAU : A.carrier ⊆ U.carrier := Set.subset_union_left
  have hBU : B.carrier ⊆ U.carrier := Set.subset_union_right
  rw [← isolationAction_eq_of_carrier_subset hAU T (atomicOnCarrier_hasLocallyAtomicAction A T hA) x,
    atomic_isolation_apply_on_larger_carrier B U hBU T hB]
  simp only [extendedAtomicCoefficient, LocallyFiniteCarrier.inclusion_val]
  exact dite_eq_right hx

/-- A recovered actual root source and complementary cone record on disjoint
carriers identify the source with the ORIGINAL weighted literal restriction. -/
theorem atomic_source_eq_originalWeightedAtomicRestriction (S A B : LocallyFiniteCarrier)
    (hdisj : Disjoint A.carrier B.carrier) (N : ℕ) (T ρ : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (hρ : AtomicOnCarrier A ρ) (hC : AtomicOnCarrier B (T - ρ)) :
    ρ = originalWeightedAtomicRestriction S A.carrier N T hT := by
  let R := originalWeightedAtomicRestriction S A.carrier N T hT
  have hRS := hasLocallyAtomicAction_atomicOnCarrier S R
    (originalWeightedAtomicRestriction_mem_strongExponent S A.carrier N T hT).1
  have hRsmall : AtomicOnCarrier (S.restrict (S.carrier ∩ A.carrier) Set.inter_subset_left) R :=
    originalWeightedAtomicRestriction_atomicOnCarrier S A.carrier N T hT
  have hRA : AtomicOnCarrier A R := hRsmall.mono
    (S := S.restrict (S.carrier ∩ A.carrier) Set.inter_subset_left)
    (fun (y : ℝ) (hy : y ∈ S.carrier ∩ A.carrier) => hy.2)
  let U := (A.union B).union S
  have hAU : A.carrier ⊆ U.carrier := fun _ hx => Or.inl (Or.inl hx)
  have hBU : B.carrier ⊆ U.carrier := fun _ hx => Or.inl (Or.inr hx)
  have hSU : S.carrier ⊆ U.carrier := Set.subset_union_right
  apply atomic_eq_of_coefficients A ρ R hρ hRA
  intro x
  let xU := LocallyFiniteCarrier.inclusion hAU x
  have hz : (T - ρ) (U.isolationSchwartz xU) = 0 := by
    apply hC
    intro y hy
    apply U.isolationSchwartz_of_mem_of_ne xU (hBU hy)
    intro he
    exact Set.disjoint_left.mp hdisj x.property (he ▸ hy)
  change T (U.isolationSchwartz xU) - ρ (U.isolationSchwartz xU) = 0 at hz
  have hRT : R (U.isolationSchwartz xU) = T (U.isolationSchwartz xU) := by
    rw [atomic_isolation_apply_on_larger_carrier S U hSU R hRS,
      atomic_isolation_apply_on_larger_carrier S U hSU T
        (hasLocallyAtomicAction_atomicOnCarrier S T hT.1)]
    change extendedAtomicCoefficient S (originalWeightedAtomicRestriction S A.carrier N T hT) x = _
    rw [originalWeightedAtomicRestriction_extendedCoefficient]
    exact ite_eq_left x.property
  rw [← isolationAction_eq_of_carrier_subset hAU ρ (atomicOnCarrier_hasLocallyAtomicAction A ρ hρ) x,
    ← isolationAction_eq_of_carrier_subset hAU R (atomicOnCarrier_hasLocallyAtomicAction A R hRA) x,
    hRT]
  exact (sub_eq_zero.mp hz).symm

end
end MeyerGeneralProblem
