module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixProjection

@[expose] public section

/-! Full Schwartz transpose tests of the actual anchor projection. Complete
original finite-prefix classification discharges their vanishing hypotheses. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- Physical transpose test of the actual residual. -/
def originalScheduledResidualPhysicalTest (bound : ℕ → ℕ) (r : ℕ)
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  f - ∑ i : Fin r, originalScheduledPrivateLineSource bound i.val f •
    originalScheduledPrefixAnchorTest bound r i

/-- Spectral transpose test of the same actual residual. -/
def originalScheduledResidualSpectralTest (bound : ℕ → ℕ) (r : ℕ)
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  - ∑ i : Fin r, 𝓕⁻ (originalScheduledPrivateLineSource bound i.val) f •
    originalScheduledPrefixAnchorTest bound r i

/-- The literal BOTH-record transpose identity holds for EVERY full distribution. -/
theorem originalScheduledResidualTest_eq (bound : ℕ → ℕ) (r : ℕ)
    (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    T (originalScheduledResidualPhysicalTest bound r f) +
      𝓕 T (originalScheduledResidualSpectralTest bound r f) =
        (T - originalScheduledAnchorProjection bound r T) f := by
  simp only [originalScheduledResidualPhysicalTest, originalScheduledResidualSpectralTest,
    originalScheduledAnchorProjection, map_sub, map_sum, map_smul, map_neg,
    sub_apply, add_apply, FourierTransform.fourierInv_sum, FourierTransform.fourierInv_smul,
    _root_.sum_apply, smul_apply, smul_eq_mul]
  simp only [mul_comm]
  ring

/-- Vanishing is derived on EVERY complete original same-exponent prefix unit ball. -/
theorem originalScheduledResidualTest_zero_prefix (bound : ℕ → ℕ) (k N : ℕ)
    (f : SchwartzMap ℝ ℂ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ originalStrongPairUnitBall (originalScheduledPrefixCarrier bound k) N) :
    T (originalScheduledResidualPhysicalTest bound (N + 1) f) +
      𝓕 T (originalScheduledResidualSpectralTest bound (N + 1) f) = 0 := by
  rw [originalScheduledResidualTest_eq,
    originalScheduledAnchorProjection_original_unit_prefix bound k N T hT, sub_self]
  rfl

/-- The actual physical residual has a derived uniform window bound, with NO
supplied zero-on-prefix or projection certificate. -/
theorem originalScheduledResidual_window_small (bound : ℕ → ℕ) (k N : ℕ)
    (f : SchwartzMap ℝ ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ R : ℝ, originalWindowRadius m ≤ R →
      ∀ (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
        (_hT : T ∈ stronglyTemperedAtomicAtExponent A N)
        (_hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent A N),
        originalStrongPairVariation A N T ≤ 1 →
        A.carrier ⊆ originalExteriorWindow (originalScheduledPrefixCarrier bound k).carrier R →
          ‖(T - originalScheduledAnchorProjection bound (N + 1) T) f‖ < ε := by
  obtain ⟨m, hm⟩ := originalStrongPair_window_observation_small
    (originalScheduledPrefixCarrier bound k) N
    (originalScheduledResidualPhysicalTest bound (N + 1) f)
    (originalScheduledResidualSpectralTest bound (N + 1) f)
    (originalScheduledResidualTest_zero_prefix bound k N f) ε hε
  refine ⟨m, ?_⟩
  intro R hR A T hT hF hu hA
  simpa only [originalScheduledResidualTest_eq] using hm R hR A T hT hF hu hA

/-- BOTH actual original residual records are simultaneously small on any
later carrier inside the derived window. The radius is a conclusion. -/
theorem originalScheduledResidual_both_window_small (bound : ℕ → ℕ) (k N : ℕ)
    (f : SchwartzMap ℝ ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ R : ℝ, originalWindowRadius m ≤ R →
      ∀ (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
        (_hT : T ∈ stronglyTemperedAtomicAtExponent A N)
        (_hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent A N),
        originalStrongPairVariation A N T ≤ 1 →
        A.carrier ⊆ originalExteriorWindow (originalScheduledPrefixCarrier bound k).carrier R →
          ‖(T - originalScheduledAnchorProjection bound (N + 1) T) f‖ +
            ‖𝓕 (T - originalScheduledAnchorProjection bound (N + 1) T) f‖ < ε := by
  obtain ⟨m₁, hm₁⟩ := originalScheduledResidual_window_small bound k N f
    (ε / 2) (half_pos hε)
  obtain ⟨m₂, hm₂⟩ := originalScheduledResidual_window_small bound k N (𝓕 f)
    (ε / 2) (half_pos hε)
  refine ⟨max m₁ m₂, ?_⟩
  intro R hR A T hT hF hu hA
  have h₁ := hm₁ R ((originalWindowRadius_strictMono.monotone (le_max_left _ _)).trans hR)
    A T hT hF hu hA
  have h₂ := hm₂ R ((originalWindowRadius_strictMono.monotone (le_max_right _ _)).trans hR)
    A T hT hF hu hA
  simpa only [TemperedDistribution.fourier_apply, add_halves] using add_lt_add h₁ h₂

end
end MeyerGeneralProblem.StrongParity
