module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalBlockProgramStability
public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalPrivateLine

@[expose] public section

/-! Literal stability of the whole original block, deletion set and source.
Proof fields and classical choices are transported through equality of their
actual input data; no equality of sources is assumed. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The real parameter family determines the whole compact block; other fields are proofs. -/
theorem CompactOriginalParameterBlock.eq_of_parameter_eq {s : ℕ}
    (a b : CompactOriginalParameterBlock s) (h : a.parameter = b.parameter) : a = b := by
  cases a
  cases b
  cases h
  rfl

variable (scales scales' : ℕ → ℕ) (hpos : ∀ i, 0 < scales i) (hpos' : ∀ i, 0 < scales' i)
  (offset s : ℕ)
  (hn : ∀ i : Fin s,
    coupledOriginalParameterNames scales hpos disjointOriginalParameterSlot (offset + i.val) =
    coupledOriginalParameterNames scales' hpos' disjointOriginalParameterSlot (offset + i.val))
include hn

/-- The actual complete real block is unchanged by equal finite certified-name data. -/
theorem coupledCompactOriginalParameterBlock_eq_of_names :
    coupledCompactOriginalParameterBlock scales hpos offset s =
      coupledCompactOriginalParameterBlock scales' hpos' offset s := by
  apply CompactOriginalParameterBlock.eq_of_parameter_eq
  funext i
  change certifiedOriginalParameterValue _ = certifiedOriginalParameterValue _
  rw [hn i]

/-- Equality holds for the ENTIRE actual physical deletion set. -/
theorem coupledComputedOriginalPhysicalDeletion_eq_of_names (hs : 2 ≤ s) (m : ℕ) :
    coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m =
      coupledComputedOriginalPhysicalDeletion scales' hpos' offset s hs m := by
  unfold coupledComputedOriginalPhysicalDeletion
  rw [coupledCompactOriginalParameterBlock_eq_of_names scales scales' hpos hpos' offset s hn,
    coupledComputedOriginalWSelectedRoots_eq_of_names scales scales' hpos hpos' offset s hn]

/-- The SAME actual normalized numerator is recovered, including its classical choice. -/
theorem coupledComputedOriginalLineNumerator_eq_of_names (hs : 2 ≤ s) (m : ℕ) :
    coupledComputedOriginalLineNumerator scales hpos offset s hs m =
      coupledComputedOriginalLineNumerator scales' hpos' offset s hs m := by
  unfold coupledComputedOriginalLineNumerator
  congr 1
  simp only [coupledCompactOriginalParameterBlock_eq_of_names scales scales' hpos hpos' offset s hn,
    coupledComputedOriginalPhysicalDeletion_eq_of_names scales scales' hpos hpos' offset s hn]

/-- The actual full original distribution, not only a selected set of coefficients, is unchanged. -/
theorem coupledComputedOriginalLineSource_eq_of_names (hs : 2 ≤ s) (m : ℕ) :
    coupledComputedOriginalLineSource scales hpos offset s hs m =
      coupledComputedOriginalLineSource scales' hpos' offset s hs m := by
  unfold coupledComputedOriginalLineSource
  rw [coupledCompactOriginalParameterBlock_eq_of_names scales scales' hpos hpos' offset s hn,
    coupledComputedOriginalLineNumerator_eq_of_names scales scales' hpos hpos' offset s hn]

/-- The literal privately dilated original source has the same finite-history stability. -/
theorem coupledComputedOriginalPrivateLineSource_eq_of_names (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) :
    coupledComputedOriginalPrivateLineSource scales hpos offset s hs m hm =
      coupledComputedOriginalPrivateLineSource scales' hpos' offset s hs m hm := by
  unfold coupledComputedOriginalPrivateLineSource
  rw [coupledComputedOriginalLineSource_eq_of_names scales scales' hpos hpos' offset s hn]

/-- The whole private physical carrier is unchanged, including every allowed zero-coefficient point. -/
theorem coupledComputedOriginalPrivatePhysicalCarrier_eq_of_names (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) :
    coupledComputedOriginalPrivatePhysicalCarrier scales hpos offset s hs m hm =
      coupledComputedOriginalPrivatePhysicalCarrier scales' hpos' offset s hs m hm := by
  rw [coupledComputedOriginalPrivatePhysicalCarrier_eq_dilate,
    coupledComputedOriginalPrivatePhysicalCarrier_eq_dilate]
  rw [coupledCompactOriginalParameterBlock_eq_of_names scales scales' hpos hpos' offset s hn,
    coupledComputedOriginalPhysicalDeletion_eq_of_names scales scales' hpos hpos' offset s hn]

end
end MeyerGeneralProblem.StrongParity
