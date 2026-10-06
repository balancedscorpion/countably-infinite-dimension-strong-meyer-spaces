module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductOriginalRows
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadLabels

@[expose] public section

/-! Complete original OriginalHeadLabels for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- Every original head row, before any noncoarse subset is selected. -/
def productOriginalHeadRow {s : ℕ} (block : CompactOriginalParameterBlock s) (p : productOriginalHeadLabel s) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ :=
  productOriginalSpectralRow block (spectralConeIndexPoint p.val)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
