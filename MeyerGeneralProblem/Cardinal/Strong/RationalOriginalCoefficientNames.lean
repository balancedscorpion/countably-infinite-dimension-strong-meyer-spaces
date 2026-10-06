module

public import MeyerGeneralProblem.Cardinal.Strong.FiniteOriginalCoefficientBounds
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginalParameterBlock

@[expose] public section

/-! Ordinary rational programs for EVERY actual compact original reciprocal
coefficient. The input precision is an explicit computed integer, and the
binary output error is proved from the constructed parameter names internally. -/

namespace MeyerGeneralProblem.StrongParity

/-- Ordinary finite rational arithmetic with a computed sensitivity precision shift. -/
def rationalNamedOriginalUpperCoefficient {s : ℕ} (names : Fin s → ℕ → ℚ)
    (k n p : ℕ) : ℚ :=
  finiteOriginalUpperCoefficient
    (fun i => names i (p + finiteOriginalUpperCoefficientSensitivity s k n)) k n

/-- An ordinary rational name for every coefficient of an internally constructed block. -/
def coupledCompactOriginalUpperCoefficientName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s k n p : ℕ) : ℚ :=
  rationalNamedOriginalUpperCoefficient
    (fun i : Fin s => (coupledOriginalParameterNames scales hpos
      disjointOriginalParameterSlot (offset + i.val)).val) k n p

/-- The input name data and finite ring computation give the requested output precision. -/
theorem rationalNamedOriginalUpperCoefficient_error {s : ℕ} (names : Fin s → ℕ → ℚ)
    (a : Fin s → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (hbounded : ∀ i p, |(names i p : ℝ)| ≤ 1)
    (herror : ∀ i p, |(names i p : ℝ) - a i| ≤ 1 / (2 : ℝ) ^ p)
    (k n p : ℕ) :
    |(rationalNamedOriginalUpperCoefficient names k n p : ℝ) -
      finiteOriginalUpperCoefficient a k n| ≤ 1 / (2 : ℝ) ^ p := by
  unfold rationalNamedOriginalUpperCoefficient
  have hmap := finiteOriginalUpperCoefficient_map (Rat.castHom ℝ)
    (fun i => names i (p + finiteOriginalUpperCoefficientSensitivity s k n)) k n
  simp only [Rat.coe_castHom] at hmap
  rw [hmap]
  exact (finiteOriginalUpperCoefficient_abs_sub_le_sensitivity _ _
    (fun i => hbounded i _) ha _ (fun i => herror i _) k n).trans
    (integer_sensitivity_binary_shift _ p)

/-- ALL actual compact original coefficients have the implemented ordinary binary names. -/
theorem coupledCompactOriginalUpperCoefficientName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s k n p : ℕ) :
    ‖(coupledCompactOriginalUpperCoefficientName scales hpos offset s k n p : ℂ) -
      compactOriginalUpperCoefficient (coupledCompactOriginalParameterBlock scales hpos offset s) k n‖ ≤
      1 / (2 : ℝ) ^ p := by
  rw [compactOriginalUpperCoefficient_eq_real_finite_formula]
  rw [← Complex.ofReal_ratCast
    (coupledCompactOriginalUpperCoefficientName scales hpos offset s k n p),
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  apply rationalNamedOriginalUpperCoefficient_error
  · intro i
    have h := (coupledCompactOriginalParameterBlock scales hpos offset s).parameter_bounds i
    rw [abs_of_pos h.1]
    linarith [h.2]
  · intro i q
    have h := coupledOriginalParameterNames_range scales hpos disjointOriginalParameterSlot (offset + i.val) q
    have hlo : (0 : ℝ) ≤ ((coupledOriginalParameterNames scales hpos
        disjointOriginalParameterSlot (offset + i.val)).val q : ℝ) := by exact_mod_cast h.1
    have hhi : ((coupledOriginalParameterNames scales hpos
        disjointOriginalParameterSlot (offset + i.val)).val q : ℝ) ≤ 1 / 2 := by
      have hh : ((coupledOriginalParameterNames scales hpos
          disjointOriginalParameterSlot (offset + i.val)).val q : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
        Rat.cast_le.mpr h.2
      norm_num at hh
      exact hh
    rw [abs_of_nonneg hlo]
    linarith
  · intro i q
    exact coupledCompactOriginalParameterBlock_name_error scales hpos offset s i q

end MeyerGeneralProblem.StrongParity
