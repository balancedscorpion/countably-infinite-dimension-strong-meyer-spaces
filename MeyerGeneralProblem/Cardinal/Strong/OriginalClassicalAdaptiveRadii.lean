module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalProtectedWindowHistory
public import MeyerGeneralProblem.Hermite.Functions

@[expose] public section

/-! Internally chosen classical adaptive radii for the actual original construction. Effective selection remains a separate obligation. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The actual BOTH-record residual condition on ALL compatible later original common carriers. -/
def originalClassicalStageRequirement (bound : ℕ → ℕ) (k R : ℕ) : Prop :=
  ∀ bound' : ℕ → ℕ, (∀ j < k, bound j = bound' j) →
    (∀ n, k ≤ n → (R : ℝ) ≤ (bound' n : ℝ)) →
    ∀ N < k, ∀ l < k, ∀ T : TemperedDistribution ℝ ℂ,
      T ∈ originalStrongPairUnitBall (originalScheduledCommonCarrier bound') N →
        ‖(T - originalScheduledAnchorProjection (originalCommonWindowBounds bound') (N + 1) T)
          (normalizedHermiteSchwartz l)‖ +
        ‖𝓕 (T - originalScheduledAnchorProjection (originalCommonWindowBounds bound') (N + 1) T)
          (normalizedHermiteSchwartz l)‖ < (1 / 2 : ℝ) ^ k

/-- A natural radius satisfying the entire finite family of actual original residual conditions exists internally. -/
theorem originalClassicalStageRequirement_exists (bound : ℕ → ℕ) (k : ℕ) :
    ∃ R : ℕ, originalClassicalStageRequirement bound k R := by
  classical
  have hi := fun i : Fin k × Fin k =>
    originalScheduledCommonCarrier_residual_all_continuations_small bound k i.1.val
      (by omega) (normalizedHermiteSchwartz i.2.val) ((1 / 2 : ℝ) ^ k) (by positivity)
  choose m hm using hi
  let M := Finset.univ.sup m
  refine ⟨2 * (M + 1), ?_⟩
  intro bound' hb hfuture N hN l hl T hT
  apply hm (⟨N, hN⟩, ⟨l, hl⟩) bound' hb ((2 * (M + 1) : ℕ) : ℝ) _ hfuture T hT
  have h := originalWindowRadius_strictMono.monotone
    (Finset.le_sup (f := m) (Finset.mem_univ (⟨N, hN⟩, ⟨l, hl⟩)))
  simpa only [M, originalWindowRadius, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using h

/-- Classical selection of the proved actual stage radius; no computable certificate-search claim. -/
def originalClassicalStageRadius (bound : ℕ → ℕ) (k : ℕ) : ℕ :=
  Classical.choose (originalClassicalStageRequirement_exists bound k)

/-- The complete internal classical adaptive bound sequence, with no input radius or escape certificate. -/
def originalClassicalAdaptiveBound : ℕ → ℕ := originalProtectedWindowBound originalClassicalStageRadius

/-- BOTH actual residual records on the completed infinite original carrier obey every later stage estimate. -/
theorem originalClassicalAdaptiveBound_residual (k N l : ℕ) (hN : N < k) (hl : l < k)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ originalStrongPairUnitBall (originalScheduledCommonCarrier originalClassicalAdaptiveBound) N) :
    ‖(T - originalScheduledAnchorProjection (originalCommonWindowBounds originalClassicalAdaptiveBound) (N + 1) T)
      (normalizedHermiteSchwartz l)‖ +
    ‖𝓕 (T - originalScheduledAnchorProjection (originalCommonWindowBounds originalClassicalAdaptiveBound) (N + 1) T)
      (normalizedHermiteSchwartz l)‖ < (1 / 2 : ℝ) ^ k := by
  have h := Classical.choose_spec (originalClassicalStageRequirement_exists
    (originalProtectedWindowHistory originalClassicalStageRadius k) k)
  apply h originalClassicalAdaptiveBound
    (fun j hj => originalProtectedWindowHistory_prefix originalClassicalStageRadius k j hj) _ N hN l hl T hT
  intro n hn
  exact_mod_cast originalProtectedWindowBound_future originalClassicalStageRadius k n hn

end
end MeyerGeneralProblem.StrongParity
