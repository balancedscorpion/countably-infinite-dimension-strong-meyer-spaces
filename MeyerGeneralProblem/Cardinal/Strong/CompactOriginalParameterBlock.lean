module

public import MeyerGeneralProblem.Cardinal.Strong.DisjointOriginalParameterSlots

@[expose] public section

/-! Actual compact distinct finite parameter blocks, constructed from the coupled family. -/

namespace MeyerGeneralProblem.StrongParity

/-- The finite original parameter data in the accepted strict compact range. -/
structure CompactOriginalParameterBlock (s : ℕ) where
  /-- Every actual real parameter of the finite original block. -/
  parameter : Fin s → ℝ
  /-- Every parameter is strictly between one quarter and one half. -/
  range : ∀ i, parameter i ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)
  /-- Distinct sheet indices have distinct actual parameters. -/
  injective : Function.Injective parameter

/-- Compact original blocks satisfy every original single-sheet domain hypothesis. -/
theorem CompactOriginalParameterBlock.parameter_bounds {s : ℕ}
    (block : CompactOriginalParameterBlock s) (i : Fin s) :
    0 < block.parameter i ∧ block.parameter i < 1 := by
  have h := block.range i
  constructor <;> linarith [h.1, h.2]

noncomputable section

/-- Every finite contiguous block of the actual coupled parameter construction,
with range and distinctness derived internally rather than supplied as certificates. -/
def coupledCompactOriginalParameterBlock (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) : CompactOriginalParameterBlock s where
  parameter i := coupledOriginalParameterValue scales hpos disjointOriginalParameterSlot (offset + i.val)
  range i := coupledOriginalParameterValue_disjoint_range scales hpos _
  injective := by
    intro i j h
    have hh := coupledOriginalParameterValue_disjoint_injective scales hpos h
    apply Fin.ext
    omega

/-- Every actual coupled block parameter has its already implemented ordinary binary name. -/
theorem coupledCompactOriginalParameterBlock_name_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (i : Fin s) (p : ℕ) :
    |((coupledOriginalParameterNames scales hpos disjointOriginalParameterSlot (offset + i.val)).val p : ℝ) -
      (coupledCompactOriginalParameterBlock scales hpos offset s).parameter i| ≤ 1 / (2 : ℝ) ^ p :=
  coupledOriginalParameterNames_error scales hpos disjointOriginalParameterSlot (offset + i.val) p

end

end MeyerGeneralProblem.StrongParity
