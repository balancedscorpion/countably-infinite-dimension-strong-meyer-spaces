module

public import MeyerGeneralProblem.Cardinal.Strong.TranslatedSpectralCone
public import MeyerGeneralProblem.Cardinal.Strong.SheetSpacing
public import MeyerGeneralProblem.Distribution.OriginalStrongEvaluation
public import MeyerGeneralProblem.Distribution.FiniteCombConvolution

@[expose] public section

/-!
# The literal Liouville mask on the full ORIGINAL strong spectral record

A single true finite difference has a global small multiplier on EVERY
translated cone point. The original weighted absolute variation controls
its actual action; no grid restriction, cutoff certificate or assumed
Fourier identity is used.
-/

namespace MeyerGeneralProblem.StrongParity
noncomputable section
open Filter
open scoped FourierTransform

/-- Literal error of the actual convergent used by the no-return mask. -/
def originalMaskError (n : ℕ) : ℝ :=
  (denominator (n + 1) : ℝ) * beta - numerator (n + 1)

/-- The actual one-step Fourier multiplier, with the inverse-Fourier sign. -/
def originalLiouvilleMask (scale : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  1 - unitPhase (-scale * (denominator (n + 1) : ℝ) * x)

/-- An exact integer-phase cancellation leaves ONLY the actual Liouville error. -/
theorem originalLiouvilleMask_integer_norm_le (scale : ℝ) (hs : scale ≠ 0)
    (n : ℕ) (p q : ℤ) :
    ‖originalLiouvilleMask scale n (((p : ℝ) + beta * (q : ℝ)) / scale)‖ ≤
      2 * Real.pi * |originalMaskError n| * |(q : ℝ)| := by
  let j : ℤ := -(denominator (n + 1) * p + numerator (n + 1) * q)
  have he : -scale * (denominator (n + 1) : ℝ) *
      (((p : ℝ) + beta * (q : ℝ)) / scale) - (j : ℝ) =
        -originalMaskError n * (q : ℝ) := by
    dsimp [j, originalMaskError]
    push_cast
    field_simp
    ring
  have h := unitPhase_norm_sub_upper (-originalMaskError n * (q : ℝ)) 0
  rw [show unitPhase 0 = 1 by simpa only [Int.cast_zero] using unitPhase_integer 0, sub_zero,
    abs_mul, abs_neg] at h
  unfold originalLiouvilleMask
  rw [norm_sub_rev]
  rw [← unitPhase_sub_integer _ j, he]
  simpa only [mul_assoc] using h

/-- Whole-carrier coordinate constant for an ordinary positive geometric scale. -/
def originalMaskConeConstant (A B : ℤ) (scale : ℝ) : ℝ :=
  scale + |translatedConeVertex A B| + |(B : ℝ)|

theorem originalMaskConeConstant_pos (A B : ℤ) (scale : ℝ) (hs : 0 < scale) :
    0 < originalMaskConeConstant A B scale := by
  unfold originalMaskConeConstant
  positivity

/-- The literal mask is small on EVERY point of the full scaled translated cone. -/
theorem originalLiouvilleMask_cone_norm_le (A B : ℤ) (scale : ℝ) (hs : 0 < scale)
    (n : ℕ) (x : (scaledTranslatedConeCarrier A B scale hs).subtype) :
    ‖originalLiouvilleMask scale n x‖ ≤
      2 * Real.pi * |originalMaskError n| * originalMaskConeConstant A B scale *
        (1 + |(x : ℝ)|) := by
  obtain ⟨z, hz⟩ := scaledTranslatedConeCarrier_label A B scale hs x
  have hcoord := translatedConeCoordinates_second_abs_le A B z
  have hf : translatedConeFrequency A B z = scale * (x : ℝ) := by
    rw [hz]
    field_simp
  have hq : |((translatedConeCoordinates A B z).2 : ℝ)| ≤
      originalMaskConeConstant A B scale * (1 + |(x : ℝ)|) := by
    rw [hf, abs_mul, abs_of_pos hs] at hcoord
    unfold originalMaskConeConstant
    have hx := abs_nonneg (x : ℝ)
    have hv := abs_nonneg (translatedConeVertex A B)
    have hb := abs_nonneg (B : ℝ)
    nlinarith
  have hmask := originalLiouvilleMask_integer_norm_le scale hs.ne' n
    (translatedConeCoordinates A B z).1 (translatedConeCoordinates A B z).2
  rw [← translatedConeFrequency_coordinates A B z, ← hz] at hmask
  calc
    _ ≤ 2 * Real.pi * |originalMaskError n| *
        |((translatedConeCoordinates A B z).2 : ℝ)| := hmask
    _ ≤ (2 * Real.pi * |originalMaskError n|) *
        (originalMaskConeConstant A B scale * (1 + |(x : ℝ)|)) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

/-- The original character used by the Schwartz operator is the literal parity phase. -/
theorem combModulationCharacter_eq_unitPhase (a x : ℝ) :
    combModulationCharacter a x = unitPhase (a * x) := by
  rw [combModulationCharacter_eq_exp]
  unfold unitPhase
  congr 1
  push_cast
  ring

/-- The TRUE finite-difference Schwartz test, not an assumed pointwise multiplier. -/
def originalMaskSchwartzTest (scale : ℝ) (n : ℕ) (h : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ :=
  h - combSchwartzModulation (-scale * (denominator (n + 1) : ℝ)) h

theorem originalMaskSchwartzTest_apply (scale : ℝ) (n : ℕ) (h : SchwartzMap ℝ ℂ)
    (x : ℝ) : originalMaskSchwartzTest scale n h x = originalLiouvilleMask scale n x * h x := by
  simp only [originalMaskSchwartzTest, sub_apply,
    combSchwartzModulation_apply, combModulationCharacter_eq_unitPhase, originalLiouvilleMask]
  ring

/-- The mask test is genuinely the inverse transform of the physical finite difference. -/
theorem fourier_originalMaskSchwartzTest (scale : ℝ) (n : ℕ) (h : SchwartzMap ℝ ℂ) :
    𝓕 (originalMaskSchwartzTest scale n h) =
      𝓕 h - combSchwartzTranslation (scale * (denominator (n + 1) : ℝ)) (𝓕 h) := by
  simp only [originalMaskSchwartzTest, sub_eq_add_neg, FourierTransform.fourier_add,
    FourierTransform.fourier_neg]
  rw [show -scale * (denominator (n + 1) : ℝ) =
      -(scale * (denominator (n + 1) : ℝ)) by ring, fourier_combSchwartzModulation_neg]

/-- Genuine original weighted-TV action bound for the literal mask on the WHOLE cone. -/
theorem originalStrong_mask_action_le (A B : ℤ) (scale : ℝ) (hs : 0 < scale)
    (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (scaledTranslatedConeCarrier A B scale hs) N)
    (n : ℕ) (h : SchwartzMap ℝ ℂ) (K : ℝ)
    (hK : ∀ x : ℝ, (1 + |x|) ^ (N + 1) * ‖h x‖ ≤ K) :
    ‖T (originalMaskSchwartzTest scale n h)‖ ≤
      (2 * Real.pi * |originalMaskError n| * originalMaskConeConstant A B scale * K) *
        ∑' x, stronglyTemperedCoefficientTerm (scaledTranslatedConeCarrier A B scale hs) N T x := by
  apply stronglyTemperedAtomicAtExponent_norm_apply_le
    (scaledTranslatedConeCarrier A B scale hs) N T hT
  intro x
  have hC : 0 < originalMaskConeConstant A B scale := originalMaskConeConstant_pos A B scale hs
  rw [originalMaskSchwartzTest_apply, norm_mul]
  calc
    _ ≤ (1 + |(x : ℝ)|) ^ N *
        (2 * Real.pi * |originalMaskError n| * originalMaskConeConstant A B scale *
          (1 + |(x : ℝ)|)) * ‖h x‖ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (originalLiouvilleMask_cone_norm_le A B scale hs n x)
          (show 0 ≤ (1 + |(x : ℝ)|) ^ N by positivity)) (norm_nonneg (h x))
    _ = (2 * Real.pi * |originalMaskError n| * originalMaskConeConstant A B scale) *
        ((1 + |(x : ℝ)|) ^ (N + 1) * ‖h x‖) := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hK x) (by positivity)

/-- The literal Liouville error pays EVERY fixed polynomial growth budget. -/
theorem originalMaskError_polynomial_tendsto_zero (k : ℕ) :
    Tendsto (fun n => (denominator (n + 1) : ℝ) ^ k * |originalMaskError n|)
      atTop (nhds 0) := scaled_coefficient_error_tendsto_zero k

end
end MeyerGeneralProblem.StrongParity
