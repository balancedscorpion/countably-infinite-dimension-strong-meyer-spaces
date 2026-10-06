module

public import MeyerGeneralProblem.Cardinal.Strong.ReturnSine

@[expose] public section

/-!
# Actual sheet roots at the original arithmetic returns

The exact real sine equation changes sign on the displacement interval
bounded by the original quarter-return error. Continuity constructs an
actual sheet root in that interval, preserving the original phases.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem sin_pi_mul_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ Real.sin (Real.pi * t) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le ht)
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1 Real.pi_pos.le)

theorem sin_pi_mul_nonpos {t : ℝ} (ht : t ≤ 0) (ht1 : -1 ≤ t) :
    Real.sin (Real.pi * t) ≤ 0 :=
  Real.sin_nonpos_of_nonpos_of_neg_pi_le
    (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le ht)
    (by simpa only [mul_neg_one] using mul_le_mul_of_nonneg_left ht1 Real.pi_pos.le)

/-- The two actual endpoint signs, with the literal original return error. -/
theorem sheetReturnSine_endpoint_signs {a ε : ℝ} (ha : 0 ≤ a) (hε : |ε| ≤ 1 / 6) :
    sheetReturnSine a ε (-|ε|) ≤ 0 ∧ 0 ≤ sheetReturnSine a ε |ε| := by
  let e := |ε|
  have he : 0 ≤ e := abs_nonneg ε
  have he6 : e ≤ 1 / 6 := hε
  have hεlo : -e ≤ ε := neg_abs_le ε
  have hεhi : ε ≤ e := le_abs_self ε
  obtain ⟨hblo, hbhi⟩ := beta_between_three_four
  have hbe_lo : 3 * e ≤ beta * e := mul_le_mul_of_nonneg_right hblo.le he
  have hbe_hi : beta * e ≤ 4 * e := mul_le_mul_of_nonneg_right hbhi.le he
  have hαlo : -1 ≤ (1 + beta) * (-e) + ε := by nlinarith
  have hαhi : (1 + beta) * (-e) + ε ≤ 0 := by nlinarith
  have hγlo : 0 ≤ (1 - beta) * (-e) - ε := by nlinarith
  have hγhi : (1 - beta) * (-e) - ε ≤ 1 := by nlinarith
  have hαlo' : 0 ≤ (1 + beta) * e + ε := by nlinarith
  have hαhi' : (1 + beta) * e + ε ≤ 1 := by nlinarith
  have hγlo' : -1 ≤ (1 - beta) * e - ε := by nlinarith
  have hγhi' : (1 - beta) * e - ε ≤ 0 := by nlinarith
  constructor
  · change sheetReturnSine a ε (-e) ≤ 0
    unfold sheetReturnSine
    exact sub_nonpos.mpr ((sin_pi_mul_nonpos hαhi hαlo).trans
      (mul_nonneg ha (sin_pi_mul_nonneg hγlo hγhi)))
  · change 0 ≤ sheetReturnSine a ε e
    unfold sheetReturnSine
    exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos ha
      (sin_pi_mul_nonpos hγhi' hγlo')).trans (sin_pi_mul_nonneg hαlo' hαhi'))

/-- The exact IVT constructs a real displacement, without a root certificate. -/
theorem exists_sheetReturnSine_zero {a ε : ℝ} (ha : 0 ≤ a) (hε : |ε| ≤ 1 / 6) :
    ∃ t : ℝ, |t| ≤ |ε| ∧ sheetReturnSine a ε t = 0 := by
  have hsign := sheetReturnSine_endpoint_signs ha hε
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc
    (by linarith [abs_nonneg ε] : -|ε| ≤ |ε|)
    (sheetReturnSine_continuous a ε).continuousOn ⟨hsign.1, hsign.2⟩
  exact ⟨t, abs_le.mpr ht, hz⟩

/-- Every sufficiently close original quarter return has an ACTUAL sheet root
within its original arithmetic error. -/
theorem exists_sheet_root_near_return {a : ℝ} (ha : 0 ≤ a) (n m : ℤ)
    (hε : |beta * n - m - 1 / 4| ≤ 1 / 6) :
    ∃ x : ℝ, sheetFlow a x = 0 ∧
      |x - (n : ℝ)| ≤ |beta * n - m - 1 / 4| := by
  obtain ⟨t, ht, hz⟩ := exists_sheetReturnSine_zero ha hε
  refine ⟨(n : ℝ) + t, ?_, ?_⟩
  · rw [sheetFlow_return_factor, hz, Complex.ofReal_zero, mul_zero]
  · simpa only [add_sub_cancel_left] using ht

end

end MeyerGeneralProblem.StrongParity
