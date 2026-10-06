module

public import MeyerGeneralProblem.Cardinal.Strong.SpectralCone
public import Mathlib.Analysis.PSeries

@[expose] public section

/-! Absolute original cone weights. Diagonals have exactly `d+1` labels,
so exponent `s+3` admits every actual degree-`s` coefficient family. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem summable_natPair_inverseCube :
    Summable (fun p : ℕ × ℕ => 1 / (1 + (p.1 : ℝ) + p.2) ^ 3) := by
  have hs : Summable (fun d : ℕ => 1 / (d + 1 : ℝ) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
      Nat.succ_injective
    simpa only [Function.comp_def, Nat.cast_succ] using h
  let e : (Σ d : ℕ, (Finset.HasAntidiagonal.antidiagonal d)) ≃ (ℕ × ℕ) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  apply e.summable_iff.mp
  change Summable (fun p : Σ d : ℕ, (Finset.HasAntidiagonal.antidiagonal d) =>
    1 / (1 + ((p.2 : ℕ × ℕ).1 : ℝ) + (p.2 : ℕ × ℕ).2) ^ 3)
  apply (summable_sigma_of_nonneg (fun p => by positivity)).mpr
  refine ⟨fun d => (hasSum_fintype _).summable, ?_⟩
  convert! hs using 1
  funext d
  rw [tsum_fintype]
  have hterm (p : Finset.HasAntidiagonal.antidiagonal d) :
      1 / (1 + ((p : ℕ × ℕ).1 : ℝ) + (p : ℕ × ℕ).2) ^ 3 =
        1 / (1 + (d : ℝ)) ^ 3 := by
    have hp := Finset.HasAntidiagonal.mem_antidiagonal.mp p.property
    have hcast : ((p : ℕ × ℕ).1 : ℝ) + (p : ℕ × ℕ).2 = d := by exact_mod_cast hp
    rw [add_assoc, hcast]
  change ∑ p : Finset.HasAntidiagonal.antidiagonal d,
    1 / (1 + ((p : ℕ × ℕ).1 : ℝ) + (p : ℕ × ℕ).2) ^ 3 = _
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    Finset.Nat.card_antidiagonal, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hd : (d + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- A proved polynomial coefficient bound gives the literal original cone weight sum. -/
theorem coneCoefficient_weight_summable (s : ℕ) (c : ℕ × ℕ → ℂ) (B : ℝ)
    (hc : ∀ p, ‖c p‖ ≤ B * ((p.1 + 1 : ℝ) ^ s / productPolydiskConstant s)) :
    Summable (fun p : ℕ × ℕ => ‖c p‖ / (1 + positiveConeFrequency p) ^ (s + 3)) := by
  have hC := productPolydiskConstant_pos s
  have hB : 0 ≤ B := by
    have h := (norm_nonneg (c (0, 0))).trans (hc (0, 0))
    simpa only [Nat.cast_zero, zero_add, one_pow, one_div, mul_nonneg_iff_of_pos_right
      (inv_pos.mpr hC)] using h
  apply Summable.of_nonneg_of_le (fun p => div_nonneg (norm_nonneg _)
    (pow_nonneg (by linarith [positiveConeFrequency_nonneg p]) _)) _
    (summable_natPair_inverseCube.mul_left (B / productPolydiskConstant s))
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
    _ ≤ (B / productPolydiskConstant s) * (1 + positiveConeFrequency p) ^ s /
        (1 + positiveConeFrequency p) ^ (s + 3) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hp0.le _)
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p.1 + 1) hk s
      exact (hc p).trans ((mul_le_mul_of_nonneg_left
        ((div_le_div_iff_of_pos_right hC).mpr hp) hB).trans_eq (by ring))
    _ = (B / productPolydiskConstant s) / (1 + positiveConeFrequency p) ^ 3 := by
      rw [pow_add]
      field_simp
    _ ≤ (B / productPolydiskConstant s) * (1 / (1 + (p.1 : ℝ) + p.2) ^ 3) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left (div_nonneg hB hC.le) (pow_pos hsum0 _)
        (pow_le_pow_left₀ hsum0.le hsum 3)

theorem productSlabUpperCoefficient_weight_summable (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    Summable (fun p : ℕ × ℕ =>
      ‖productSlabUpperCoefficient s r p.1 p.2‖ / (1 + positiveConeFrequency p) ^ (s + 3)) :=
  coneCoefficient_weight_summable s _ (productSlabCoefficientBound s r)
    (fun p => productSlabUpperCoefficient_norm_le s r p.1 p.2)

theorem productSlabLowerCoefficient_weight_summable (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    Summable (fun p : ℕ × ℕ =>
      ‖productSlabLowerCoefficient s r p.1 p.2‖ / (1 + positiveConeFrequency p) ^ (s + 3)) :=
  coneCoefficient_weight_summable s _ (productSlabCoefficientBound s r)
    (fun p => productSlabLowerCoefficient_norm_le s r p.1 p.2)

end

end MeyerGeneralProblem.StrongParity
