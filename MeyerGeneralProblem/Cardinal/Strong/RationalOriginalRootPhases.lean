module

public import MeyerGeneralProblem.Cardinal.Strong.RationalBetaShiftNames
public import MeyerGeneralProblem.Cardinal.Strong.CoupledCompactOriginalCarriers
public import MeyerGeneralProblem.Cardinal.Strong.RationalNamedRootSearch

@[expose] public section

/-! Ordinary binary names for BOTH original flow phases at EVERY labelled
root of the actual internally constructed compact block. -/

namespace MeyerGeneralProblem.StrongParity

/-- The ordinary native original-root name on the internally constructed compact block. -/
def coupledCompactOriginalNativeRootName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (i : Fin s) (n : ℤ) (p : ℕ) : ℚ :=
  rationalNamedOriginalRootApprox
    (coupledOriginalParameterNames scales hpos disjointOriginalParameterSlot (offset + i.val)).val n p

/-- Ordinary first flow-phase program at every original native root. -/
def coupledCompactOriginalRootUName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (i : Fin s) (n : ℤ) (p : ℕ) : ℚ × ℚ :=
  rationalNamedUnitPhase (coupledCompactOriginalNativeRootName scales hpos offset s i n) p

/-- Ordinary second quarter-shifted flow-phase program at every original native root. -/
def coupledCompactOriginalRootVName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (i : Fin s) (n : ℤ) (p : ℕ) : ℚ × ℚ :=
  rationalNamedUnitPhase
    (rationalNamedBetaShift (coupledCompactOriginalNativeRootName scales hpos offset s i n)) p

noncomputable section

/-- All native original-root errors follow from the actual parameter-name construction. -/
theorem coupledCompactOriginalNativeRootName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (i : Fin s) (n : ℤ) (p : ℕ) :
    |(coupledCompactOriginalNativeRootName scales hpos offset s i n p : ℝ) -
      compactOriginalRootLabel n
        ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter i)| ≤ 1 / (2 : ℝ) ^ p := by
  rw [compactOriginalRootLabel_eq n
    ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter_bounds i).1.le
    ((coupledCompactOriginalParameterBlock scales hpos offset s).range i).2.le]
  exact rationalNamedOriginalRootApprox_error _
    ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter_bounds i).1.le
    ((coupledCompactOriginalParameterBlock scales hpos offset s).range i).2.le
    (coupledOriginalParameterNames_range scales hpos disjointOriginalParameterSlot (offset + i.val))
    (coupledCompactOriginalParameterBlock_name_error scales hpos offset s i) n p

/-- Every actual labelled root's first complex phase has the implemented binary error. -/
theorem coupledCompactOriginalRootUName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (i : Fin s) (n : ℤ) (p : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalRootUName scales hpos offset s i n p) -
      unitPhase (compactOriginalRootLabel n
        ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter i))‖ ≤ 1 / (2 : ℝ) ^ p :=
  rationalNamedUnitPhase_error _ (coupledCompactOriginalNativeRootName_error scales hpos offset s i n) p

/-- Every actual labelled root's SECOND quarter-shifted phase has the implemented binary error. -/
theorem coupledCompactOriginalRootVName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (i : Fin s) (n : ℤ) (p : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalRootVName scales hpos offset s i n p) -
      unitPhase (beta * compactOriginalRootLabel n
        ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter i) - 1 / 4)‖ ≤
          1 / (2 : ℝ) ^ p :=
  rationalNamedUnitPhase_error _
    (rationalNamedBetaShift_error _ (coupledCompactOriginalNativeRootName_error scales hpos offset s i n)) p

/-- First-phase program values obey the safe finite arithmetic bound. -/
theorem coupledCompactOriginalRootUName_norm_le_two (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (i : Fin s) (n : ℤ) (p : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalRootUName scales hpos offset s i n p)‖ ≤ 2 :=
  rationalNamedUnitPhase_norm_le_two _ p

/-- Second-phase program values obey the same safe finite arithmetic bound. -/
theorem coupledCompactOriginalRootVName_norm_le_two (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (i : Fin s) (n : ℤ) (p : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalRootVName scales hpos offset s i n p)‖ ≤ 2 :=
  rationalNamedUnitPhase_norm_le_two _ p

end

end MeyerGeneralProblem.StrongParity
