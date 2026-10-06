module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductResidues
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductPoleJump
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPoleMass

@[expose] public section

/-! Original ProductPoleJump for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- The actual continuous remainder has a genuine open neighborhood at every
root of the complete original product. -/
theorem productPoleRemainder_continuousOn {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : (compactOriginalProductSheetCarrier block).subtype) :
    ContinuousOn (productPoleRemainder block r x)
      (simplePoleRegularDomain (compactOriginalComplexSheetProduct block) (x : ℂ)) := by
  have hroot : compactOriginalComplexSheetProduct block (x : ℂ) = 0 := by
    rw [compactOriginalComplexSheetProduct_ofReal block]
    exact x.property
  exact simplePoleRemainder_continuousOn _ _ _
    (fun z => (compactOriginalComplexSheetProduct_hasDerivAt block z).differentiableAt)
    (complexProductSlabNumerator_differentiable s r)
    (compactOriginalComplexSheetProduct_deriv_ne_zero block hroot)

/-- The integrated jump of each ACTUAL original principal part equals its
original physical mass against every Schwartz test. -/
theorem productPoleJump_integral_tendsto {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : (compactOriginalProductSheetCarrier block).subtype) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun t : ℝ => ∫ y : ℝ, realPoleJump (productPoleResidue block r x) x t y * f y)
      (𝓝[>] 0) (𝓝 (productPhysicalResidue block r x * f x)) := by
  rw [← productPoleResidue_original_mass]
  exact realPoleJump_integral_tendsto _ f.integrable f.continuous.continuousAt

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
