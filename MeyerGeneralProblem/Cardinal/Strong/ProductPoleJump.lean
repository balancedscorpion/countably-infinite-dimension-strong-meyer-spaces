module

public import MeyerGeneralProblem.Cardinal.Strong.ProductPoleMass
public import MeyerGeneralProblem.Cardinal.Strong.CauchyJump

@[expose] public section

/-! Integrated principal parts at every actual original product root.
This does not yet claim that the entire quotient's compact jump is their sum. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- The actual continuous remainder has a genuine open neighborhood at every
root of the complete original product. -/
theorem productPoleRemainder_continuousOn (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : (productSheetCarrier s).subtype) :
    ContinuousOn (productPoleRemainder s r x)
      (simplePoleRegularDomain (complexSheetProduct s) (x : ℂ)) := by
  have hroot : complexSheetProduct s (x : ℂ) = 0 := by
    rw [complexSheetProduct_ofReal]
    exact x.property
  exact simplePoleRemainder_continuousOn _ _ _
    (fun z => (complexSheetProduct_hasDerivAt s z).differentiableAt)
    (complexProductSlabNumerator_differentiable s r)
    (complexSheetProduct_deriv_ne_zero s hroot)

/-- The integrated jump of each ACTUAL original principal part equals its
original physical mass against every Schwartz test. -/
theorem productPoleJump_integral_tendsto (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : (productSheetCarrier s).subtype) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun t : ℝ => ∫ y : ℝ, realPoleJump (productPoleResidue s r x) x t y * f y)
      (𝓝[>] 0) (𝓝 (productPhysicalResidue s r x * f x)) := by
  rw [← productPoleResidue_original_mass]
  exact realPoleJump_integral_tendsto _ f.integrable f.continuous.continuousAt

end

end MeyerGeneralProblem.StrongParity
