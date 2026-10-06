module

public import MeyerGeneralProblem.Cardinal.Strong.SimplePoleRemainder
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-! The literal normalized real Cauchy kernel is an actual peak family.
Its nonnegativity, integral and decay are proved, not supplied as a
Plemelj or delta-limit certificate. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- The original normalized Cauchy profile on the real line. -/
def cauchyPeakProfile (x : ℝ) : ℝ := Real.pi⁻¹ * (1 + x ^ 2)⁻¹

theorem cauchyPeakProfile_nonneg (x : ℝ) : 0 ≤ cauchyPeakProfile x := by
  unfold cauchyPeakProfile
  positivity

theorem cauchyPeakProfile_integral : (∫ x : ℝ, cauchyPeakProfile x) = 1 := by
  unfold cauchyPeakProfile
  rw [integral_const_mul, integral_univ_inv_one_add_sq, inv_mul_cancel₀ Real.pi_ne_zero]

theorem cauchyPeakProfile_decay :
    Tendsto (fun x : ℝ => ‖x‖ * cauchyPeakProfile x) (Bornology.cobounded ℝ) (𝓝 0) := by
  have hb (x : ℝ) : ‖x‖ * cauchyPeakProfile x ≤ Real.pi⁻¹ * ‖x‖⁻¹ := by
    have hs : x ^ 2 = ‖x‖ ^ 2 := by simp only [Real.norm_eq_abs, sq_abs]
    have hr : ‖x‖ / (1 + ‖x‖ ^ 2) ≤ ‖x‖⁻¹ := by
      by_cases hx : ‖x‖ = 0
      · simp [hx]
      · have hp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
        rw [inv_eq_one_div]
        exact (div_le_div_iff₀ (by positivity) hp).mpr (by nlinarith)
    calc
      _ = Real.pi⁻¹ * (‖x‖ / (1 + ‖x‖ ^ 2)) := by
        unfold cauchyPeakProfile
        rw [hs]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr Real.pi_pos.le)
  have h := (tendsto_inv_atTop_zero.comp
    (tendsto_norm_cobounded_atTop (E := ℝ))).const_mul Real.pi⁻¹
  apply squeeze_zero (fun x => mul_nonneg (norm_nonneg _) (cauchyPeakProfile_nonneg x)) hb
  convert! h using 1
  simp only [mul_zero]

/-- Scaling the actual Cauchy profile gives the literal delta limit on integrable tests. -/
theorem cauchyPeak_integral_tendsto {g : ℝ → ℂ} {a : ℝ}
    (hg : Integrable g) (hga : ContinuousAt g a) :
    Tendsto (fun c : ℝ => ∫ x : ℝ, (c * cauchyPeakProfile (c * (a - x))) • g x)
      atTop (𝓝 (g a)) := by
  have hdecay : Tendsto (fun x : ℝ => ‖x‖ ^ Module.finrank ℝ ℝ * cauchyPeakProfile x)
      (Bornology.cobounded ℝ) (𝓝 0) := by
    simpa only [Module.finrank_self, pow_one] using cauchyPeakProfile_decay
  convert! tendsto_integral_comp_smul_smul_of_integrable'
    cauchyPeakProfile_nonneg cauchyPeakProfile_integral hdecay hg hga using 1
  funext c
  simp only [Module.finrank_self, pow_one, smul_eq_mul]

end

end MeyerGeneralProblem.StrongParity
