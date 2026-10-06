module

public import MeyerGeneralProblem.Cardinal.Strong.SheetDerivative
public import MeyerGeneralProblem.Carrier.LocallyFinite
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inverse

@[expose] public section

/-!
# Actual real sheet flow and simple roots

The formal torus-direction derivative is identified with the derivative
of the literal complex-valued function on the real line. Its zeros are
therefore isolated, without a supplied root regularity assumption.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The original sheet evaluated on the original real quarter-phase flow. -/
def sheetFlow (a x : ℝ) : ℂ :=
  sheetPolynomial a (unitPhase x) (unitPhase (beta * x - 1 / 4))

theorem unitPhase_hasDerivAt (x : ℝ) :
    HasDerivAt unitPhase ((2 * Real.pi : ℝ) * Complex.I * unitPhase x) x := by
  change HasDerivAt (fun t : ℝ => Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) _ x
  have h := (((hasDerivAt_id x).const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  simpa [unitPhase, id_eq, mul_assoc, mul_comm, mul_left_comm] using h

/-- Chain and product rules recover the literal torus-direction derivative. -/
theorem sheetFlow_hasDerivAt (a x : ℝ) :
    HasDerivAt (sheetFlow a)
      ((2 * Real.pi : ℝ) * Complex.I *
        sheetTorusDerivative a (unitPhase x) (unitPhase (beta * x - 1 / 4))) x := by
  have hZ := unitPhase_hasDerivAt x
  have hinner : HasDerivAt (fun y : ℝ => beta * y - 1 / 4) beta x := by
    simpa using (((hasDerivAt_id x).const_mul beta).sub_const (1 / 4))
  have hW := (unitPhase_hasDerivAt (beta * x - 1 / 4)).scomp x hinner
  have h := (((hasDerivAt_const x (1 : ℂ)).sub (hW.const_mul (a : ℂ))).add
    (hZ.const_mul (a : ℂ))).sub (hZ.mul hW)
  convert! h using 1
  simp only [sheetTorusDerivative, Complex.real_smul, Function.comp_apply]
  push_cast
  ring

theorem sheetFlow_deriv_ne_zero {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hroot : sheetFlow a x = 0) : deriv (sheetFlow a) x ≠ 0 := by
  rw [(sheetFlow_hasDerivAt a x).deriv]
  apply mul_ne_zero
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero
  · exact sheetTorusDerivative_ne_zero ha ha1 (unitPhase_norm _) hroot

/-- Every actual real root is isolated in the real line. -/
theorem sheetFlow_root_isolated {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hroot : sheetFlow a x = 0) :
    ∀ᶠ y in nhdsWithin x {x}ᶜ, sheetFlow a y ≠ 0 := by
  have hd := sheetFlow_hasDerivAt a x
  have hn : (2 * Real.pi : ℝ) * Complex.I *
      sheetTorusDerivative a (unitPhase x) (unitPhase (beta * x - 1 / 4)) ≠ 0 := by
    rw [← hd.deriv]
    exact sheetFlow_deriv_ne_zero ha ha1 hroot
  simpa only [hroot] using hd.eventually_ne hn

/-- The complete real zero set of one original sheet. -/
def sheetRoots (a : ℝ) : Set ℝ := {x | sheetFlow a x = 0}

theorem sheetRoots_isClosed (a : ℝ) : IsClosed (sheetRoots a) := by
  apply isClosed_eq
  · exact continuous_iff_continuousAt.mpr fun x => (sheetFlow_hasDerivAt a x).continuousAt
  · exact continuous_const

theorem sheetRoots_isDiscrete {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    IsDiscrete (sheetRoots a) := by
  apply isDiscrete_iff_nhdsNE.mpr
  intro x hx
  apply Filter.inf_principal_eq_bot.mpr
  exact sheetFlow_root_isolated ha ha1 hx

/-- Compact intervals meet the whole actual sheet in finitely many roots. -/
theorem sheetRoots_finite_inter_Icc {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (u v : ℝ) :
    (sheetRoots a ∩ Set.Icc u v).Finite :=
  (isCompact_Icc.inter_left (sheetRoots_isClosed a)).finite
    ((sheetRoots_isDiscrete ha ha1).mono Set.inter_subset_left)

/-- The actual original sheet, packaged without a supplied finiteness certificate. -/
def sheetCarrier (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) : LocallyFiniteCarrier where
  carrier := sheetRoots a
  finite_inter_Icc := sheetRoots_finite_inter_Icc ha ha1

end

end MeyerGeneralProblem.StrongParity
