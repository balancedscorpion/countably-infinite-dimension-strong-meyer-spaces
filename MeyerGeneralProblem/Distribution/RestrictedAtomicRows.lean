module

public import MeyerGeneralProblem.Distribution.CarrierUnion
public import MeyerGeneralProblem.Distribution.CarrierInclusion
public import MeyerGeneralProblem.Carrier.FiniteModificationDensity

@[expose] public section

/-! Actual original zero rows characterize support on any subcarrier.
The reverse implication uses compact Schwartz action and full cutoff density;
strong variation transports through the literal inclusion of original points. -/

namespace MeyerGeneralProblem

noncomputable section

open Filter
open scoped Topology

theorem atomicOnCarrier_restrict_iff (S : LocallyFiniteCarrier) (A : Set ℝ)
    (hA : A ⊆ S.carrier) (T : TemperedDistribution ℝ ℂ) :
    AtomicOnCarrier (S.restrict A hA) T ↔ AtomicOnCarrier S T ∧
      ∀ x : S.subtype, (x : ℝ) ∉ A → T (S.isolationSchwartz x) = 0 := by
  constructor
  · intro hT
    refine ⟨hT.mono hA, ?_⟩
    intro x hx
    apply hT
    intro y hy
    exact S.isolationSchwartz_of_mem_of_ne x (hA hy) (fun h => hx (h ▸ hy))
  · rintro ⟨hT, hrow⟩ f hf
    have hcompact (g : SchwartzMap ℝ ℂ) (hg : HasCompactSupport g)
        (hgf : SchwartzVanishesOn (S.restrict A hA) g) : T g = 0 := by
      obtain ⟨E, _, heq⟩ := atomicOnCarrier_isLocallyAtomicCoefficientFamily S T hT g hg
      rw [heq]
      apply Finset.sum_eq_zero
      intro x _
      change T (S.isolationSchwartz x) * g x = 0
      by_cases hx : (x : ℝ) ∈ A
      · rw [hgf x hx, mul_zero]
      · rw [hrow x hx, zero_mul]
    have hzero : ∀ N : ℕ, T (compactSchwartzApproximation N f) = 0 := fun N =>
      hcompact _ (compactSchwartzApproximation_hasCompactSupport N f)
        (compactSchwartzApproximation_preserves_vanishing _ N f hf)
    have hlim := (T.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
    have hlim0 : Tendsto (fun N => T (compactSchwartzApproximation N f)) atTop (𝓝 0) := by
      simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique hlim hlim0

/-- Deletion of actual carrier points is exactly vanishing of their ORIGINAL
canonical coefficients, rather than a row condition on a chosen forward image. -/
theorem atomicOnCarrier_delete_iff (S : LocallyFiniteCarrier) (D : Set ℝ)
    (T : TemperedDistribution ℝ ℂ) :
    AtomicOnCarrier (S.delete D) T ↔ AtomicOnCarrier S T ∧
      ∀ x : S.subtype, (x : ℝ) ∈ D → T (S.isolationSchwartz x) = 0 := by
  rw [LocallyFiniteCarrier.delete, atomicOnCarrier_restrict_iff]
  constructor
  · rintro ⟨hT, hrow⟩
    refine ⟨hT, fun x hx => hrow x ?_⟩
    exact fun h => h.2 hx
  · rintro ⟨hT, hrow⟩
    refine ⟨hT, fun x hx => hrow x ?_⟩
    by_contra h
    exact hx ⟨x.property, h⟩

/-- At a fixed exponent, the original variation on an ACTUAL smaller support
is the restriction of the original larger-carrier variation. -/
theorem stronglyTemperedAtomicAtExponent_restrict (S : LocallyFiniteCarrier)
    (A : Set ℝ) (hA : A ⊆ S.carrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (S.restrict A hA) T)
    (hS : T ∈ stronglyTemperedAtomicAtExponent S N) :
    T ∈ stronglyTemperedAtomicAtExponent (S.restrict A hA) N := by
  let R := S.restrict A hA
  have hlocal : HasLocallyAtomicAction R T := atomicOnCarrier_hasLocallyAtomicAction R T hT
  refine ⟨hlocal, ?_⟩
  have hincl : R.carrier ⊆ S.carrier := hA
  have h := hS.2.comp_injective (LocallyFiniteCarrier.inclusion hincl).injective
  convert! h using 1
  funext x
  exact (stronglyTemperedCoefficientTerm_inclusion hincl T hlocal N x).symm

theorem stronglyTemperedAtomicAtExponent_delete (S : LocallyFiniteCarrier)
    (D : Set ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (S.delete D) T)
    (hS : T ∈ stronglyTemperedAtomicAtExponent S N) :
    T ∈ stronglyTemperedAtomicAtExponent (S.delete D) N :=
  stronglyTemperedAtomicAtExponent_restrict S _ Set.sdiff_subset N T hT hS

/-- Enlarging the ACTUAL atomic support zero-pads the original coefficient
record, preserving its summability at the SAME exponent. -/
theorem stronglyTemperedAtomicAtExponent_mono_carrier {S U : LocallyFiniteCarrier}
    (hSU : S.carrier ⊆ U.carrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    T ∈ stronglyTemperedAtomicAtExponent U N := by
  have hlocal := hT.1
  have hatomic := hasLocallyAtomicAction_atomicOnCarrier S T hlocal
  refine ⟨hasLocallyAtomicAction_of_carrier_subset hSU T hlocal, ?_⟩
  apply ((LocallyFiniteCarrier.inclusion hSU).injective.summable_iff ?_).mp
  · simpa only [Function.comp_def, stronglyTemperedCoefficientTerm_inclusion hSU T hlocal] using
      hT.2
  · intro y hy
    have hz : T (U.isolationSchwartz y) = 0 := by
      apply hatomic
      intro x hx
      apply U.isolationSchwartz_of_mem_of_ne y (hSU hx)
      intro hxy
      exact hy ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    simp only [stronglyTemperedCoefficientTerm, hz, norm_zero, zero_div]

end

end MeyerGeneralProblem
