module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalCoefficientNames

@[expose] public section

/-! Uniform computed sizes of the actual original coefficients and ALL their
ordinary rational names. The constructed parameter-range inputs are internal. -/

namespace MeyerGeneralProblem.StrongParity

/-- Every internally generated parameter name has absolute value at most one. -/
theorem coupledCompactOriginalParameterName_abs_le_one (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (i : Fin s) (p : ℕ) :
    |((coupledOriginalParameterNames scales hpos
      disjointOriginalParameterSlot (offset + i.val)).val p : ℝ)| ≤ 1 := by
  have h := coupledOriginalParameterNames_range scales hpos disjointOriginalParameterSlot (offset + i.val) p
  have hlo : (0 : ℝ) ≤ ((coupledOriginalParameterNames scales hpos
      disjointOriginalParameterSlot (offset + i.val)).val p : ℝ) := by exact_mod_cast h.1
  have hhi : ((coupledOriginalParameterNames scales hpos
      disjointOriginalParameterSlot (offset + i.val)).val p : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
    Rat.cast_le.mpr h.2
  norm_num at hhi
  rw [abs_of_nonneg hlo]
  linarith

/-- All ordinary reciprocal-name outputs satisfy their computed integer size. -/
theorem rationalNamedOriginalUpperCoefficient_abs_le_size {s : ℕ} (names : Fin s → ℕ → ℚ)
    (hbounded : ∀ i p, |(names i p : ℝ)| ≤ 1) (k n p : ℕ) :
    |(rationalNamedOriginalUpperCoefficient names k n p : ℝ)| ≤
      (finiteOriginalUpperCoefficientSize s k n : ℝ) := by
  unfold rationalNamedOriginalUpperCoefficient
  have hmap := finiteOriginalUpperCoefficient_map (Rat.castHom ℝ)
    (fun i => names i (p + finiteOriginalUpperCoefficientSensitivity s k n)) k n
  simp only [Rat.coe_castHom] at hmap
  rw [hmap]
  exact finiteOriginalUpperCoefficient_abs_le_size _ (fun i => hbounded i _) k n

/-- EVERY internally generated original reciprocal name has a uniform complex size. -/
theorem coupledCompactOriginalUpperCoefficientName_norm_le_size (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s k n p : ℕ) :
    ‖(coupledCompactOriginalUpperCoefficientName scales hpos offset s k n p : ℂ)‖ ≤
      (finiteOriginalUpperCoefficientSize s k n : ℝ) := by
  rw [← Complex.ofReal_ratCast
    (coupledCompactOriginalUpperCoefficientName scales hpos offset s k n p),
    Complex.norm_real, Real.norm_eq_abs]
  exact rationalNamedOriginalUpperCoefficient_abs_le_size _
    (coupledCompactOriginalParameterName_abs_le_one scales hpos offset s) k n p

/-- EVERY actual compact original reciprocal coefficient has the computed integer size. -/
theorem compactOriginalUpperCoefficient_norm_le_size {s : ℕ}
    (block : CompactOriginalParameterBlock s) (k n : ℕ) :
    ‖compactOriginalUpperCoefficient block k n‖ ≤ (finiteOriginalUpperCoefficientSize s k n : ℝ) := by
  rw [compactOriginalUpperCoefficient_eq_real_finite_formula, Complex.norm_real, Real.norm_eq_abs]
  apply finiteOriginalUpperCoefficient_abs_le_size
  intro i
  have h := block.parameter_bounds i
  rw [abs_of_pos h.1]
  linarith [h.2]

end MeyerGeneralProblem.StrongParity
