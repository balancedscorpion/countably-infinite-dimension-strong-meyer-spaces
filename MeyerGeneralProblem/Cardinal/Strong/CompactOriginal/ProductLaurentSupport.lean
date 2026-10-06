module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductAnnihilator
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductLaurentSupport

@[expose] public section

/-! Complete original ProductLaurentSupport for actual compact parameter blocks.
Every original supported pair is retained, without a constructed-image premise. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open scoped Pointwise

theorem productLaurentCoefficients_support_box {s : ℕ} (block : CompactOriginalParameterBlock s) {n : ℤ × ℤ}
    (hn : n ∈ (productLaurentCoefficients block).support) :
    0 ≤ n.1 ∧ n.1 ≤ s ∧ 0 ≤ n.2 ∧ n.2 ≤ s := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    finiteSheetLaurentProduct_support_box Finset.univ (block.parameter) hn

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
