module

public import MeyerGeneralProblem.Distribution.CombScaling
public import MeyerGeneralProblem.Distribution.FiniteCombConvolution
public import MeyerGeneralProblem.Cardinal.Strong.ParityLimit

@[expose] public section

/-!
# Actual Fourier envelopes for polynomially shrinking physical tests

Translation and dilation are the actual continuous Schwartz operators.
The inverse Fourier formula retains the inverse absolute Jacobian;
pointwise polynomial envelopes are derived from fixed Schwartz seminorms.
-/
namespace MeyerGeneralProblem
noncomputable section
open scoped FourierTransform

/-- The physical test φ(d*(x-t)) for ordinary positive scale d. -/
def originalShrinkingTest (d : ℝ) (hd : 0 < d) (t : ℝ) (φ : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ :=
  combSchwartzTranslation (-t) (combSchwartzDilation d hd.ne' φ)

theorem originalShrinkingTest_apply (d : ℝ) (hd : 0 < d) (t : ℝ)
    (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    originalShrinkingTest d hd t φ x = φ (d * (x - t)) := by
  simp only [originalShrinkingTest, combSchwartzTranslation_apply, combSchwartzDilation_apply]
  congr 1
  ring

/-- The true inverse transform has exact shrinking Jacobian d^-1 and unit-modulus phase. -/
theorem norm_fourierInv_originalShrinkingTest (d : ℝ) (hd : 0 < d) (t : ℝ)
    (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖(𝓕⁻ (originalShrinkingTest d hd t φ)) x‖ = d⁻¹ * ‖(𝓕⁻ φ) (x / d)‖ := by
  have hf (g : SchwartzMap ℝ ℂ) (y : ℝ) : (𝓕⁻ g) y = (𝓕 g) (-y) := rfl
  rw [hf, originalShrinkingTest, fourier_combSchwartzTranslation, norm_mul,
    norm_combModulationCharacter, one_mul, fourier_combSchwartzDilation, norm_smul,
    Real.norm_eq_abs, abs_abs, abs_of_pos (inv_pos.mpr hd)]
  rw [hf]
  congr 2
  ring

/-- The fixed pointweight constant is a genuine finite supremum of Schwartz seminorms. -/
def originalPointweightBound (M : ℕ) (h : SchwartzMap ℝ ℂ) : ℝ :=
  2 ^ M * (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) h

theorem originalPointweightBound_nonneg (M : ℕ) (h : SchwartzMap ℝ ℂ) :
    0 ≤ originalPointweightBound M h := by
  unfold originalPointweightBound
  positivity

theorem originalPointweightBound_apply (M : ℕ) (h : SchwartzMap ℝ ℂ) (x : ℝ) :
    (1 + |x|) ^ M * ‖h x‖ ≤ originalPointweightBound M h := by
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (M, 0)) (k := M) (n := 0) le_rfl le_rfl h x
  convert! hb using 1;
    norm_num [originalPointweightBound, Real.norm_eq_abs, norm_iteratedFDeriv_zero,
      schwartzSeminormFamily]

/-- A uniform envelope on the WHOLE inverse transform, with exact polynomial scale. -/
theorem originalShrinkingTest_fourierInv_pointweight_le (d : ℝ) (hd : 1 ≤ d) (t : ℝ)
    (φ : SchwartzMap ℝ ℂ) (M : ℕ) (x : ℝ) :
    (1 + |x|) ^ M * ‖(𝓕⁻ (originalShrinkingTest d (lt_of_lt_of_le zero_lt_one hd) t φ)) x‖ ≤
      d ^ M / d * originalPointweightBound M (𝓕⁻ φ) := by
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hw : (1 + |x|) ^ M ≤ d ^ M * (1 + |x / d|) ^ M := by
    rw [← mul_pow]
    gcongr
    rw [abs_div, abs_of_pos hdpos]
    have he : d * (1 + |x| / d) = d + |x| := by field_simp
    rw [he]
    linarith
  rw [norm_fourierInv_originalShrinkingTest]
  calc
    _ ≤ (d ^ M * (1 + |x / d|) ^ M) * (d⁻¹ * ‖(𝓕⁻ φ) (x / d)‖) := by
      gcongr
    _ = (d ^ M / d) * ((1 + |x / d|) ^ M * ‖(𝓕⁻ φ) (x / d)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (originalPointweightBound_apply M (𝓕⁻ φ) (x / d))
      (by positivity)

namespace StrongParity

/-- Actual quartically shrinking physical test along the literal Liouville denominators. -/
def originalQuarticShrinkingTest (n : ℕ) (t : ℝ) (φ : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ :=
  originalShrinkingTest ((denominator (n + 1) : ℝ) ^ 4)
    (pow_pos (by exact_mod_cast denominator_pos (n + 1)) 4) t φ

/-- Quartic localization costs exactly b^(4N) at spectral pointweight N+1. -/
theorem originalQuarticShrinkingTest_fourierInv_pointweight_le (n : ℕ) (t : ℝ)
    (φ : SchwartzMap ℝ ℂ) (N : ℕ) (x : ℝ) :
    (1 + |x|) ^ (N + 1) * ‖(𝓕⁻ (originalQuarticShrinkingTest n t φ)) x‖ ≤
      (denominator (n + 1) : ℝ) ^ (4 * N) * originalPointweightBound (N + 1) (𝓕⁻ φ) := by
  have hb : (1 : ℝ) ≤ denominator (n + 1) := by
    exact_mod_cast denominator_pos (n + 1)
  have hd : (1 : ℝ) ≤ (denominator (n + 1) : ℝ) ^ 4 := one_le_pow₀ hb
  have h := originalShrinkingTest_fourierInv_pointweight_le
    ((denominator (n + 1) : ℝ) ^ 4) hd t φ (N + 1) x
  convert! h using 1
  rw [pow_succ, mul_div_cancel_right₀ _ (by positivity), ← pow_mul]

end StrongParity
end
end MeyerGeneralProblem
