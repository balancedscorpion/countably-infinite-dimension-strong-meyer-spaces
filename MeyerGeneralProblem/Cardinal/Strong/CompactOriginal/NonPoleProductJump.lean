module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.DampedFourierIntegral
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.DampedTubeJump
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPoleMass
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.NonPoleProductJump
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.LocalProductJump

@[expose] public section

/-! Original NonPoleProductJump for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open Filter MeasureTheory
open scoped Topology FourierTransform

theorem complexProductSlabQuotient_measurable {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    Measurable (complexProductSlabQuotient block r) := by
  have hf : Differentiable ℂ (compactOriginalComplexSheetProduct block) :=
    fun z => (compactOriginalComplexSheetProduct_hasDerivAt block z).differentiableAt
  exact (complexProductSlabNumerator_differentiable s r).continuous.measurable.div
    hf.continuous.measurable

/-- The actual quotient jump contributes zero on every test in a positive
neighborhood of any point outside the COMPLETE original root carrier. -/
theorem productTubeJump_local_nonpole_tendsto {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (a : ℝ) (ha : a ∉ (compactOriginalProductSheetCarrier block).carrier) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, f x ≠ 0 → |x - a| ≤ δ) →
      Tendsto (fun t : ℝ => ∫ x : ℝ, productTubeJump block r t x * f x)
        (𝓝[>] 0) (𝓝 0) := by
  have hf : Differentiable ℂ (compactOriginalComplexSheetProduct block) :=
    fun z => (compactOriginalComplexSheetProduct_hasDerivAt block z).differentiableAt
  have hnonzero : compactOriginalComplexSheetProduct block (a : ℂ) ≠ 0 := by
    rw [compactOriginalComplexSheetProduct_ofReal block]
    exact ha
  let U : Set ℂ := {z | compactOriginalComplexSheetProduct block z ≠ 0}
  have hopen : IsOpen U := isOpen_ne_fun hf.continuous continuous_const
  have hcont : ContinuousOn (complexProductSlabQuotient block r) U :=
    (complexProductSlabNumerator_differentiable s r).continuous.continuousOn.div
      hf.continuous.continuousOn (fun _ hz => hz)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hnonzero)
  refine ⟨ρ / 4, by positivity, ?_⟩
  intro f hsupport
  have hclosed : Metric.closedBall (a : ℂ) (2 * (ρ / 4)) ⊆ U := by
    intro z hz
    apply hρsub
    apply Metric.mem_ball.mpr
    have hz' := Metric.mem_closedBall.mp hz
    linarith
  exact continuousRemainder_jump_integral_tendsto _ a (by positivity)
    (complexProductSlabQuotient_measurable block r) (hcont.mono hclosed) f hsupport

/-- Inverse Fourier zero action of the actual complete spectral record away
from the complete original physical carrier. -/
theorem productSpectral_fourierInv_local_nonpole {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (a : ℝ) (ha : a ∉ (compactOriginalProductSheetCarrier block).carrier) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, f x ≠ 0 → |x - a| ≤ δ) → (𝓕⁻ (productSpectralDistribution block r)) f = 0 := by
  obtain ⟨δ, hδ, hlim⟩ := productTubeJump_local_nonpole_tendsto block r a ha
  refine ⟨δ, hδ, ?_⟩
  intro f hf
  exact tendsto_nhds_unique (productTubeJump_integral_tendsto_spectral block r f) (hlim f hf)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
