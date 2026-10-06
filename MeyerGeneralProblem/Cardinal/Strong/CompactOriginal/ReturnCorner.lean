module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductResidues
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ReturnCorner

@[expose] public section

/-! Complete original ReturnCorner for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open Filter
open scoped Topology

/-- The chosen actual root as a point of the COMPLETE finite-product carrier. -/
def privateProductSheetRoot {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) (n : ℕ) : (compactOriginalProductSheetCarrier block).subtype :=
  productSheetRootInclusion block i
    ⟨privateSheetRoot (block.parameter i) (block.parameter_bounds i).1.le n,
      privateSheetRoot_is_root _ _ n⟩

/-- Actual escape gives the cofinite carrier filter, without an injective
enumeration hypothesis or any assertion that selected roots exhaust the carrier. -/
theorem privateProductSheetRoot_tendsto_cofinite {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) :
    Tendsto (privateProductSheetRoot block i) atTop cofinite := by
  change map (privateProductSheetRoot block i) atTop ≤ cofinite
  apply le_cofinite_iff_eventually_ne.mpr
  intro y
  change ∀ᶠ n in atTop, privateProductSheetRoot block i n ≠ y
  filter_upwards [(privateSheetRoot_abs_tendsto_atTop (block.parameter i)
    (block.parameter_bounds i).1.le).eventually_gt_atTop |(y : ℝ)|] with n hn
  intro heq
  have hval := congrArg (fun x : (compactOriginalProductSheetCarrier block).subtype => |(x : ℝ)|) heq
  exact (ne_of_gt hn) hval

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
