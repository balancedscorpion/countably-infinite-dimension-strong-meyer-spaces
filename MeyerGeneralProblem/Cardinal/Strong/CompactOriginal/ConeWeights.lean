module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ReciprocalSlabSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SlabCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ConeWeights

@[expose] public section

/-! Original ConeWeights for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- A proved polynomial coefficient bound gives the literal original cone weight sum. -/
theorem coneCoefficient_weight_summable {s : ℕ} (block : CompactOriginalParameterBlock s) (c : ℕ × ℕ → ℂ) (B : ℝ)
    (hc : ∀ p, ‖c p‖ ≤ B * ((p.1 + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block)) :
    Summable (fun p : ℕ × ℕ => ‖c p‖ / (1 + positiveConeFrequency p) ^ (s + 3)) := by
  have hC := compactOriginalPolydiskConstant_pos block
  have hB : 0 ≤ B := by
    have h := (norm_nonneg (c (0, 0))).trans (hc (0, 0))
    simpa only [Nat.cast_zero, zero_add, one_pow, one_div, mul_nonneg_iff_of_pos_right
      (inv_pos.mpr hC)] using h
  apply Summable.of_nonneg_of_le (fun p => div_nonneg (norm_nonneg _)
    (pow_nonneg (by linarith [positiveConeFrequency_nonneg p]) _)) _
    (summable_natPair_inverseCube.mul_left (B / compactOriginalPolydiskConstant block))
  intro p
  have hp0 : 0 < 1 + positiveConeFrequency p := by
    linarith [positiveConeFrequency_nonneg p]
  have hsum0 : 0 < 1 + (p.1 : ℝ) + p.2 := by positivity
  have hb : 1 ≤ beta := le_trans (by norm_num) beta_between_three_four.1.le
  have hk : (p.1 + 1 : ℝ) ≤ 1 + positiveConeFrequency p := by
    linarith [(positiveConeFrequency_coordinate_le p).1]
  have hsum : 1 + (p.1 : ℝ) + p.2 ≤ 1 + positiveConeFrequency p := by
    unfold positiveConeFrequency
    have hn : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
    nlinarith
  calc
    _ ≤ (B / compactOriginalPolydiskConstant block) * (1 + positiveConeFrequency p) ^ s /
        (1 + positiveConeFrequency p) ^ (s + 3) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hp0.le _)
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p.1 + 1) hk s
      exact (hc p).trans ((mul_le_mul_of_nonneg_left
        ((div_le_div_iff_of_pos_right hC).mpr hp) hB).trans_eq (by ring))
    _ = (B / compactOriginalPolydiskConstant block) / (1 + positiveConeFrequency p) ^ 3 := by
      rw [pow_add]
      field_simp
    _ ≤ (B / compactOriginalPolydiskConstant block) * (1 / (1 + (p.1 : ℝ) + p.2) ^ 3) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left (div_nonneg hB hC.le) (pow_pos hsum0 _)
        (pow_le_pow_left₀ hsum0.le hsum 3)

theorem productSlabUpperCoefficient_weight_summable {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    Summable (fun p : ℕ × ℕ =>
      ‖productSlabUpperCoefficient block r p.1 p.2‖ / (1 + positiveConeFrequency p) ^ (s + 3)) :=
  coneCoefficient_weight_summable block _ (productSlabCoefficientBound s r)
    (fun p => productSlabUpperCoefficient_norm_le block r p.1 p.2)

theorem productSlabLowerCoefficient_weight_summable {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    Summable (fun p : ℕ × ℕ =>
      ‖productSlabLowerCoefficient block r p.1 p.2‖ / (1 + positiveConeFrequency p) ^ (s + 3)) :=
  coneCoefficient_weight_summable block _ (productSlabCoefficientBound s r)
    (fun p => productSlabLowerCoefficient_norm_le block r p.1 p.2)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
