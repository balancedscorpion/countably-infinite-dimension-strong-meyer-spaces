module

public import MeyerGeneralProblem.Distribution.FiniteConvolutionCoefficients
public import Mathlib.Data.Finsupp.Basic

@[expose] public section

/-!
# Original spectral arrays and their literal annihilator recurrence

The array is recovered from an arbitrary atomic Fourier distribution. It is
extended by zero off the spectral carrier; no forward-image restriction is
made. Local finiteness is inherited through an injective frequency map.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped SchwartzMap FourierTransform

variable {G : Type*} [AddCommGroup G]

/-- Finite Laurent coefficients acting on the entire original spectral array. -/
def annihilatorArrayConvolution (p : G →₀ ℂ) (u : G → ℂ) (n : G) : ℂ :=
  ∑ m ∈ p.support, p m * u (n - m)

/-- The literal positive exponential symbol of those finite coefficients. -/
def annihilatorExponentialSymbol (L : G →+ ℝ) (p : G →₀ ℂ) (x : ℝ) : ℂ :=
  ∑ m ∈ p.support, p m * combModulationCharacter (L m) x

/-- The canonical original Fourier array, including every zero-extended entry. -/
def originalFourierArray (L : G →+ ℝ) (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (n : G) : ℂ :=
  extendedAtomicCoefficient S (𝓕 T) (L n)

/-- Local finiteness of actual frequency support, expressed on array indices. -/
def FrequencyLocallyFinite (L : G →+ ℝ) (u : G → ℂ) : Prop :=
  ∀ a b : ℝ, {n : G | u n ≠ 0 ∧ L n ∈ Set.Icc a b}.Finite

theorem originalFourierArray_frequencyLocallyFinite (L : G →+ ℝ)
    (hL : Function.Injective L) (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) :
    FrequencyLocallyFinite L (originalFourierArray L S T) := by
  intro a b
  apply ((S.finite_inter_Icc a b).preimage (Set.injOn_of_injective hL)).subset
  intro n hn
  refine ⟨?_, hn.2⟩
  by_contra hnot
  exact hn.1 (by simp [originalFourierArray, extendedAtomicCoefficient, hnot])

/-- An arbitrary original atomic Fourier pair satisfies the literal finite
Laurent recurrence whenever the actual physical symbol vanishes on its carrier. -/
theorem originalFourierArray_annihilated (L : G →+ ℝ) (p : G →₀ ℂ)
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier A T) (hFT : AtomicOnCarrier B (𝓕 T))
    (hz : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) :
    ∀ n, annihilatorArrayConvolution p (originalFourierArray L B T) n = 0 := by
  classical
  let a : p.support → ℝ := fun m => L m
  let c : p.support → ℂ := fun m => p m
  have hs (x : ℝ) (hx : x ∈ A.carrier) :
      ∑ m : p.support, c m * combModulationCharacter (a m) x = 0 := by
    change (∑ m : p.support, (fun m : G => p m * combModulationCharacter (L m) x) m) = 0
    rw [p.support.sum_coe_sort (fun m : G => p m * combModulationCharacter (L m) x)]
    exact hz x hx
  have hv := finiteCombConvolution_fourier_eq_zero A T hT a c hs
  intro n
  have hc := extendedAtomicCoefficient_finiteCombConvolution B (𝓕 T) hFT a c (L n)
  rw [hv] at hc
  have hc0 : (∑ m : p.support, p m * extendedAtomicCoefficient B (𝓕 T)
      (L n - L m)) = 0 := by
    simpa [extendedAtomicCoefficient, a, c] using hc.symm
  rw [p.support.sum_coe_sort
    (fun m : G => p m * extendedAtomicCoefficient B (𝓕 T) (L n - L m))] at hc0
  simpa only [annihilatorArrayConvolution, originalFourierArray, map_sub] using hc0

end

end MeyerGeneralProblem
