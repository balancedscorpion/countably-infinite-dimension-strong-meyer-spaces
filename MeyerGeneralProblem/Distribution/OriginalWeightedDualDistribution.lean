module

public import MeyerGeneralProblem.Distribution.OriginalWeightedAtomicDual
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section

/-! Genuine weighted dual Fourier-pair records on FULL Schwartz space.
The physical and spectral records are continuous Schwartz functionals built
from the actual original weighted C0 tests. ALL observations are weak-star continuous. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty FourierTransform

/-- The physical full Schwartz test in the actual two-record C0 predual. -/
def originalWeightedPhysicalTestCLM (N : ℕ) :
    SchwartzMap ℝ ℂ →L[ℂ] (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) :=
  (originalWeightedSchwartzC0CLM N).prod 0

/-- The spectral full Schwartz test in the SAME actual two-record C0 predual. -/
def originalWeightedSpectralTestCLM (N : ℕ) :
    SchwartzMap ℝ ℂ →L[ℂ] (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) :=
  (0 : SchwartzMap ℝ ℂ →L[ℂ] C₀(ℝ, ℂ)).prod (originalWeightedSchwartzC0CLM N)

/-- ALL physical tests retain the literal original weighted C0 test. -/
theorem originalWeightedPhysicalTestCLM_apply (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    originalWeightedPhysicalTestCLM N f = (originalWeightedSchwartzC0 N f, 0) := rfl

/-- ALL spectral tests retain the literal original weighted C0 test. -/
theorem originalWeightedSpectralTestCLM_apply (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    originalWeightedSpectralTestCLM N f = (0, originalWeightedSchwartzC0 N f) := rfl

/-- Genuine WHOLE physical tempered distribution of an actual weighted weak dual. -/
def originalWeightedDualPhysicalDistribution (N : ℕ) (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) :
    TemperedDistribution ℝ ℂ :=
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) (SchwartzMap ℝ ℂ) ℂ
    ((WeakDual.toStrongDual q).comp (originalWeightedPhysicalTestCLM N))

/-- Genuine WHOLE spectral tempered distribution of the SAME actual weighted weak dual. -/
def originalWeightedDualSpectralDistribution (N : ℕ) (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) :
    TemperedDistribution ℝ ℂ :=
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) (SchwartzMap ℝ ℂ) ℂ
    ((WeakDual.toStrongDual q).comp (originalWeightedSpectralTestCLM N))

/-- EVERY original full physical Schwartz observation is an actual weighted dual evaluation. -/
theorem originalWeightedDualPhysicalDistribution_apply (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (f : SchwartzMap ℝ ℂ) :
    originalWeightedDualPhysicalDistribution N q f = q (originalWeightedSchwartzC0 N f, 0) := rfl

/-- EVERY original full spectral Schwartz observation is an actual weighted dual evaluation. -/
theorem originalWeightedDualSpectralDistribution_apply (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (f : SchwartzMap ℝ ℂ) :
    originalWeightedDualSpectralDistribution N q f = q (0, originalWeightedSchwartzC0 N f) := rfl

/-- Every FULL physical Schwartz observation is weak-star continuous. -/
theorem originalWeightedDualPhysicalDistribution_eval_continuous (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    Continuous (fun q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) =>
      originalWeightedDualPhysicalDistribution N q f) :=
  WeakDual.eval_continuous (originalWeightedSchwartzC0 N f, 0)

/-- Every FULL spectral Schwartz observation is weak-star continuous. -/
theorem originalWeightedDualSpectralDistribution_eval_continuous (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    Continuous (fun q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) =>
      originalWeightedDualSpectralDistribution N q f) :=
  WeakDual.eval_continuous (0, originalWeightedSchwartzC0 N f)

/-- The GENUINE whole Fourier equation is exactly equality of ALL original weighted tests. -/
theorem originalWeightedDualFourierGraph_iff (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) :
    originalWeightedDualSpectralDistribution N q = 𝓕 (originalWeightedDualPhysicalDistribution N q) ↔
      ∀ f : SchwartzMap ℝ ℂ,
        q (0, originalWeightedSchwartzC0 N f) = q (originalWeightedSchwartzC0 N (𝓕 f), 0) := by
  constructor
  · intro h f
    have he := congrArg (fun D : TemperedDistribution ℝ ℂ => D f) h
    simpa only [originalWeightedDualSpectralDistribution_apply, TemperedDistribution.fourier_apply,
      originalWeightedDualPhysicalDistribution_apply] using he
  · intro h
    ext f
    exact h f

/-- Fourier compatibility of the genuine WHOLE original records is weak-star closed. -/
theorem originalWeightedDualFourierGraph_isClosed (N : ℕ) :
    IsClosed {q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) |
      originalWeightedDualSpectralDistribution N q = 𝓕 (originalWeightedDualPhysicalDistribution N q)} := by
  have he : {q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) |
      originalWeightedDualSpectralDistribution N q = 𝓕 (originalWeightedDualPhysicalDistribution N q)} =
      ⋂ f : SchwartzMap ℝ ℂ, {q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) |
        q (0, originalWeightedSchwartzC0 N f) = q (originalWeightedSchwartzC0 N (𝓕 f), 0)} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, originalWeightedDualFourierGraph_iff]
  rw [he]
  apply isClosed_iInter
  intro f
  exact isClosed_eq (WeakDual.eval_continuous _) (WeakDual.eval_continuous _)

/-- The actual weak-star compact unit ball with the GENUINE Fourier graph imposed.
Identifying its support-constrained duals with original strong atomic records is a separate obligation. -/
def originalWeightedDualFourierPairBall (N : ℕ) : Set (WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) :=
  (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1) ∩
    {q | originalWeightedDualSpectralDistribution N q = 𝓕 (originalWeightedDualPhysicalDistribution N q)}

/-- The weighted dual Fourier-pair unit ball is compact, derived internally
from actual Banach-Alaoglu and the genuine original Fourier equation. -/
theorem originalWeightedDualFourierPairBall_isCompact (N : ℕ) :
    IsCompact (originalWeightedDualFourierPairBall N) :=
  (WeakDual.isCompact_closedBall (0 : StrongDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) 1).inter_right
    (originalWeightedDualFourierGraph_isClosed N)

end
end MeyerGeneralProblem
