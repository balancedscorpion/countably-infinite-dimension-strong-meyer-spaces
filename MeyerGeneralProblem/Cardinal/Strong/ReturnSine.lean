module

public import MeyerGeneralProblem.Cardinal.Strong.PhysicalDistribution
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# Literal sine equation for roots near the original quarter returns

Integer periodicity and an exact complex sine identity reduce the actual
sheet at `n+t` to a real equation. Its endpoint signs supply actual
nearby roots by the intermediate value theorem, without an argument-lift
or root-location certificate.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem unitPhase_sine_chord (u v : ℝ) :
    unitPhase u - unitPhase v =
      2 * Complex.I * unitPhase ((u + v) / 2) * (Real.sin (Real.pi * (u - v)) : ℂ) := by
  let E := unitPhase ((u + v) / 2)
  let z : ℂ := (Real.pi * (u - v) : ℝ)
  have hleft : E * Complex.exp (-z * Complex.I) = unitPhase v := by
    dsimp [E, z, unitPhase]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hright : E * Complex.exp (z * Complex.I) = unitPhase u := by
    dsimp [E, z, unitPhase]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hs : 2 * (Real.sin (Real.pi * (u - v)) : ℂ) =
      (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I := by
    rw [Complex.ofReal_sin]
    exact Complex.two_sin z
  symm
  calc
    _ = E * Complex.I * (2 * (Real.sin (Real.pi * (u - v)) : ℂ)) := by dsimp [E]; ring
    _ = (E * (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I))) *
        (Complex.I * Complex.I) := by rw [hs]; ring
    _ = -(E * Complex.exp (-z * Complex.I) - E * Complex.exp (z * Complex.I)) := by
      rw [Complex.I_mul_I, mul_sub]
      ring
    _ = _ := by rw [hleft, hright]; ring

theorem sheetPolynomial_sine_factor (a u v : ℝ) :
    sheetPolynomial a (unitPhase u) (unitPhase v) =
      -2 * Complex.I * unitPhase ((u + v) / 2) *
        ((Real.sin (Real.pi * (u + v)) - a * Real.sin (Real.pi * (u - v)) : ℝ) : ℂ) := by
  have hzero : unitPhase (0 : ℝ) = 1 := by simp [unitPhase]
  have hs := unitPhase_sine_chord (u + v) 0
  simp only [add_zero, sub_zero, hzero] at hs
  have hp : sheetPolynomial a (unitPhase u) (unitPhase v) =
      -(unitPhase (u + v) - 1) + (a : ℂ) * (unitPhase u - unitPhase v) := by
    rw [unitPhase_add]
    unfold sheetPolynomial
    ring
  rw [hp, hs, unitPhase_sine_chord]
  push_cast
  ring

/-- The exact real sine equation in the displacement and original return error. -/
def sheetReturnSine (a ε t : ℝ) : ℝ :=
  Real.sin (Real.pi * ((1 + beta) * t + ε)) -
    a * Real.sin (Real.pi * ((1 - beta) * t - ε))

theorem sheetReturnSine_continuous (a ε : ℝ) : Continuous (sheetReturnSine a ε) := by
  unfold sheetReturnSine
  fun_prop

/-- The original quarter-flow sheet at the actual signed integer return. -/
theorem sheetFlow_return_factor (a : ℝ) (n m : ℤ) (t : ℝ) :
    sheetFlow a ((n : ℝ) + t) =
      -2 * Complex.I * unitPhase (((1 + beta) * t + (beta * n - m - 1 / 4)) / 2) *
        (sheetReturnSine a (beta * n - m - 1 / 4) t : ℂ) := by
  have hZ : unitPhase ((n : ℝ) + t) = unitPhase t := by
    rw [unitPhase_add, unitPhase_integer, one_mul]
  have hW : unitPhase (beta * ((n : ℝ) + t) - 1 / 4) =
      unitPhase (beta * t + (beta * n - m - 1 / 4)) := by
    rw [show beta * ((n : ℝ) + t) - 1 / 4 =
      (beta * t + (beta * n - m - 1 / 4)) + m by ring,
      unitPhase_add, unitPhase_integer, mul_one]
  unfold sheetFlow
  rw [hZ, hW, sheetPolynomial_sine_factor]
  rw [show t + (beta * t + (beta * n - m - 1 / 4)) =
    (1 + beta) * t + (beta * n - m - 1 / 4) by ring,
    show t - (beta * t + (beta * n - m - 1 / 4)) =
      (1 - beta) * t - (beta * n - m - 1 / 4) by ring]
  rfl

end

end MeyerGeneralProblem.StrongParity
