module

public import MeyerGeneralProblem.Cardinal.Strong.SheetPowerSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.TaylorSeries

@[expose] public section

/-! Finite arithmetic for the actual original sheet Taylor coefficients.
The recurrence below uses only ring operations and natural powers.  Its value
is proved equal to the derivative-defined coefficient of the original sheet. -/

namespace MeyerGeneralProblem.StrongParity

open scoped Topology

/-- A finite ring program for every original single-sheet reciprocal coefficient. -/
def sheetFiniteWCoefficient {R : Type*} [CommRing R] (a : R) : ℕ → ℕ → R
  | 0, n => a ^ n
  | k + 1, 0 => (-a) ^ (k + 1)
  | k + 1, n + 1 => a * sheetFiniteWCoefficient a (k + 1) n +
      sheetFiniteWCoefficient a k n - a * sheetFiniteWCoefficient a k (n + 1)
termination_by k n => (k, n)

noncomputable section

/-- Normalized derivatives at zero, with no assumed numerical oracle. -/
def originalTaylorCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / (n.factorial : ℂ)

@[simp] theorem originalTaylorCoefficient_zero (f : ℂ → ℂ) :
    originalTaylorCoefficient f 0 = f 0 := by
  simp [originalTaylorCoefficient]

theorem originalTaylorCoefficient_eventuallyEq {f g : ℂ → ℂ}
    (h : f =ᶠ[nhds 0] g) (n : ℕ) :
    originalTaylorCoefficient f n = originalTaylorCoefficient g n := by
  rw [originalTaylorCoefficient, originalTaylorCoefficient, h.iteratedDeriv_eq n]

theorem originalTaylorCoefficient_sub {f g : ℂ → ℂ} (n : ℕ)
    (hf : ContDiffAt ℂ n f 0) (hg : ContDiffAt ℂ n g 0) :
    originalTaylorCoefficient (fun W => f W - g W) n =
      originalTaylorCoefficient f n - originalTaylorCoefficient g n := by
  simp only [originalTaylorCoefficient, iteratedDeriv_fun_sub hf hg, sub_div]

theorem originalTaylorCoefficient_const_mul (a : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    originalTaylorCoefficient (fun W => a * f W) n = a * originalTaylorCoefficient f n := by
  simp only [originalTaylorCoefficient, iteratedDeriv_const_mul_field, mul_div_assoc]

theorem originalTaylorCoefficient_variable_mul {f : ℂ → ℂ} (n : ℕ)
    (hf : ContDiffAt ℂ (n + 1) f 0) :
    originalTaylorCoefficient (fun W => W * f W) (n + 1) =
      originalTaylorCoefficient f n := by
  have hD : iteratedDeriv (n + 1) (fun W : ℂ => W * f W) 0 =
      (n + 1 : ℂ) * iteratedDeriv n f 0 := by
    rw [iteratedDeriv_fun_mul (f := fun W : ℂ => W) contDiffAt_id hf]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro i hi hi1
      simp [iteratedDeriv_fun_id_zero, hi1]
    · simp
  have hnf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  rw [originalTaylorCoefficient, hD, originalTaylorCoefficient, Nat.factorial_succ]
  push_cast
  field_simp

theorem originalTaylorCoefficient_denominator_mul {f : ℂ → ℂ} (a : ℂ) (n : ℕ)
    (hf : ContDiffAt ℂ (n + 1) f 0) :
    originalTaylorCoefficient (fun W => (1 - a * W) * f W) (n + 1) =
      originalTaylorCoefficient f (n + 1) - a * originalTaylorCoefficient f n := by
  have hfun : (fun W => (1 - a * W) * f W) =
      (fun W => f W - a * (W * f W)) := by funext W; ring
  rw [hfun, originalTaylorCoefficient_sub (n + 1) hf (by fun_prop),
    originalTaylorCoefficient_const_mul, originalTaylorCoefficient_variable_mul n hf]

theorem originalTaylorCoefficient_numerator_mul {f : ℂ → ℂ} (a : ℂ) (n : ℕ)
    (hf : ContDiffAt ℂ (n + 1) f 0) :
    originalTaylorCoefficient (fun W => (W - a) * f W) (n + 1) =
      originalTaylorCoefficient f n - a * originalTaylorCoefficient f (n + 1) := by
  have hfun : (fun W => (W - a) * f W) =
      (fun W => W * f W - a * f W) := by funext W; ring
  rw [hfun, originalTaylorCoefficient_sub (n + 1) (by fun_prop) (by fun_prop),
    originalTaylorCoefficient_const_mul, originalTaylorCoefficient_variable_mul n hf]

theorem sheetZCoefficient_analyticAt_zero (a : ℝ) (k : ℕ) :
    AnalyticAt ℂ (sheetZCoefficient a k) 0 := by
  unfold sheetZCoefficient sheetBlaschke
  fun_prop (disch := simp)

/-- The actual denominator can be canceled throughout a neighborhood of zero. -/
theorem sheetZCoefficient_denominator_eventually_ne_zero (a : ℝ) :
    ∀ᶠ W : ℂ in nhds 0, (1 : ℂ) - a * W ≠ 0 := by
  have h : ContinuousAt (fun W : ℂ => (1 : ℂ) - a * W) 0 := by fun_prop
  exact h.eventually_ne (by simp : (1 : ℂ) - a * (0 : ℂ) ≠ 0)

theorem sheetZCoefficient_zero_taylor (a : ℝ) (n : ℕ) :
    originalTaylorCoefficient (sheetZCoefficient a 0) n = (a : ℂ) ^ n := by
  induction n with
  | zero => simp [sheetZCoefficient]
  | succ n ih =>
    have heq : (fun W => (1 - (a : ℂ) * W) * sheetZCoefficient a 0 W)
        =ᶠ[nhds 0] (fun _ => (1 : ℂ)) := by
      filter_upwards [sheetZCoefficient_denominator_eventually_ne_zero a] with W hW
      simp [sheetZCoefficient, hW]
    have h := originalTaylorCoefficient_eventuallyEq heq (n + 1)
    rw [originalTaylorCoefficient_denominator_mul (a : ℂ) n
      (sheetZCoefficient_analyticAt_zero a 0).contDiffAt] at h
    have hzero : originalTaylorCoefficient (fun _ => (1 : ℂ)) (n + 1) = 0 := by
      simp [originalTaylorCoefficient, iteratedDeriv_const]
    rw [hzero, ih] at h
    rw [pow_succ]
    linear_combination h

theorem sheetZCoefficient_successor_taylor (a : ℝ) (k n : ℕ) :
    originalTaylorCoefficient (sheetZCoefficient a (k + 1)) (n + 1) =
      (a : ℂ) * originalTaylorCoefficient (sheetZCoefficient a (k + 1)) n +
      originalTaylorCoefficient (sheetZCoefficient a k) n -
      (a : ℂ) * originalTaylorCoefficient (sheetZCoefficient a k) (n + 1) := by
  have heq : (fun W => (1 - (a : ℂ) * W) * sheetZCoefficient a (k + 1) W)
      =ᶠ[nhds 0] (fun W => (W - a) * sheetZCoefficient a k W) := by
    filter_upwards [sheetZCoefficient_denominator_eventually_ne_zero a] with W hW
    unfold sheetZCoefficient sheetBlaschke
    rw [pow_succ]
    field_simp [hW]
  have h := originalTaylorCoefficient_eventuallyEq heq (n + 1)
  rw [originalTaylorCoefficient_denominator_mul (a : ℂ) n
    (sheetZCoefficient_analyticAt_zero a (k + 1)).contDiffAt,
    originalTaylorCoefficient_numerator_mul (a : ℂ) n
    (sheetZCoefficient_analyticAt_zero a k).contDiffAt] at h
  linear_combination h

/-- Every output of the finite ring program is the actual original sheet coefficient. -/
theorem sheetFiniteWCoefficient_eq_taylor (a : ℝ) (k n : ℕ) :
    sheetFiniteWCoefficient (a : ℂ) k n =
      originalTaylorCoefficient (sheetZCoefficient a k) n := by
  induction k generalizing n with
  | zero => simpa [sheetFiniteWCoefficient] using (sheetZCoefficient_zero_taylor a n).symm
  | succ k ih =>
    induction n with
    | zero => simp [sheetFiniteWCoefficient, sheetZCoefficient, sheetBlaschke]
    | succ n ihn =>
      rw [sheetFiniteWCoefficient, ihn, ih n, ih (n + 1),
        sheetZCoefficient_successor_taylor]

end

end MeyerGeneralProblem.StrongParity
