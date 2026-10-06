module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Statement of record for the strongly tempered countable-dimensional case.
Fourier normalization is exp(-2πixξ); support containment is intended.
The only proof placeholder is the theorem below. -/

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

/-- One locally finite carrier has a whole strongly tempered Meyer space
of complex Hamel dimension ℵ₀. Both actual atomic records satisfy weighted
absolute summability; membership is not merely membership in their span. -/
theorem strongCardinalClaim :
    ∃ Λ : Set ℝ, LocallyFinite Λ ∧
      Module.rank ℂ (strongMeyerSpace Λ) = Cardinal.aleph0 ∧
      (∀ T : TemperedDistribution ℝ ℂ,
        T ∈ strongMeyerSpace Λ ↔ StronglyAtomic Λ T ∧
          StronglyAtomic Λ (FourierTransform.fourier T)) := by
  sorry

end CountablyInfiniteStrongCrystallineMeasures
