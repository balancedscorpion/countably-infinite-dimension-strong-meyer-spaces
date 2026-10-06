module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalClassicalStrongCountable
public import Mathlib.LinearAlgebra.Dimension.Constructions

-- Ensure identical complex topology elaboration in the two interfaces.
attribute [-instance] instCommCStarAlgebraComplex in
section

@[expose] public section
noncomputable section
namespace CountablyInfiniteStrongCrystallineMeasures

/-- Every bounded closed interval meets the carrier in finitely many points. -/
def LocallyFinite (Λ : Set ℝ) : Prop :=
  ∀ a b : ℝ, (Λ ∩ Set.Icc a b).Finite

/-- Local atomic action and finite polynomially weighted absolute variation.
The same coefficients serve every compactly supported Schwartz test. -/
def StronglyAtomic (Λ : Set ℝ) (T : TemperedDistribution ℝ ℂ) : Prop :=
  ∃ a : Λ → ℂ,
    (∀ f : SchwartzMap ℝ ℂ, HasCompactSupport f →
      ∃ E : Finset Λ,
        (∀ x : Λ, x ∉ E → f x = 0) ∧ T f = ∑ x ∈ E, a x * f x) ∧
    ∃ N : ℕ, Summable (fun x : Λ => ‖a x‖ / (1 + |(x : ℝ)|) ^ N)

/-- The algebraic span of the two-record strong class. The main theorem
proves that membership is exactly the class itself, on the same carrier. -/
def strongMeyerSpace (Λ : Set ℝ) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  Submodule.span ℂ {T | StronglyAtomic Λ T ∧
    StronglyAtomic Λ (FourierTransform.fourier T)}

open MeyerGeneralProblem MeyerGeneralProblem.StrongParity

private theorem strong_iff (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    StronglyAtomic S.carrier T ↔ T ∈ StronglyTemperedAtomicOnCarrier S := by
  rw [mem_stronglyTemperedAtomicOnCarrier_iff]
  constructor
  · rintro ⟨a, ha, N, hN⟩
    refine ⟨N, ⟨a, ha⟩, ?_⟩
    have heq : a = fun x => T (S.isolationSchwartz x) := by
      funext x
      exact locallyAtomicCoefficient_eq_isolationAction S T a ha x
    rw [heq] at hN
    exact hN
  · rintro ⟨N, ⟨a, ha⟩, hN⟩
    refine ⟨a, ha, N, ?_⟩
    have heq : a = fun x => T (S.isolationSchwartz x) := by
      funext x
      exact locallyAtomicCoefficient_eq_isolationAction S T a ha x
    rw [heq]
    exact hN

private theorem space_eq (S : LocallyFiniteCarrier) :
    strongMeyerSpace S.carrier = StronglyTemperedMeyerSpace S := by
  have hset : {T | StronglyAtomic S.carrier T ∧
      StronglyAtomic S.carrier (FourierTransform.fourier T)} =
      (StronglyTemperedMeyerSpace S : Set (TemperedDistribution ℝ ℂ)) := by
    ext T
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, strong_iff,
      mem_stronglyTemperedMeyerSpace_iff]
  unfold strongMeyerSpace
  rw [hset, Submodule.span_eq]

/-- One locally finite carrier has a whole strongly tempered Meyer space
of complex Hamel dimension ℵ₀. Both actual atomic records satisfy weighted
absolute summability; membership is not merely membership in their span. -/
theorem strongCardinalClaim :
    ∃ Λ : Set ℝ, LocallyFinite Λ ∧
      Module.rank ℂ (strongMeyerSpace Λ) = Cardinal.aleph0 ∧
      (∀ T : TemperedDistribution ℝ ℂ,
        T ∈ strongMeyerSpace Λ ↔ StronglyAtomic Λ T ∧
          StronglyAtomic Λ (FourierTransform.fourier T)) := by
  obtain ⟨S, hS⟩ := exists_stronglyTemperedMeyerSpace_rank_aleph0
  refine ⟨S.carrier, S.finite_inter_Icc, ?_, ?_⟩
  · rw [space_eq]
    exact hS
  · intro T
    rw [space_eq, mem_stronglyTemperedMeyerSpace_iff, ← strong_iff, ← strong_iff]

end CountablyInfiniteStrongCrystallineMeasures
end
