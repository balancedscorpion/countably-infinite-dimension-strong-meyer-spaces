module

public import MeyerGeneralProblem.Distribution.OriginalWindowDualIntersection

@[expose] public section

/-! Uniform residual bounds from the ACTUAL nested compact weighted Fourier
window balls and their internally proved exact intersection. Radius bounds
are conclusions, not input certificates. The subsequent actual finite-mode
projection and terminating effective certificate search are separate steps. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty FourierTransform

/-- Every genuine continuous dual observation zero on the actual supported
intersection is uniformly small on a sufficiently large REAL exterior window. -/
theorem originalWeightedDualWindowBall_uniform_small (S : LocallyFiniteCarrier) (N : ℕ)
    (ψ : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) → ℂ) (hψ : Continuous ψ)
    (hzero : ∀ q ∈ originalWeightedDualSupportedFourierPairBall S N, ψ q = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ R : ℝ, originalWindowRadius k ≤ R →
      ∀ q ∈ originalWeightedDualWindowBall S N R, ‖ψ q‖ < ε := by
  have hsmall : ∃ k : ℕ, ∀ q ∈ originalWeightedDualWindowBall S N (originalWindowRadius k),
      ‖ψ q‖ < ε := by
    by_contra h
    push Not at h
    let B (n : ℕ) := originalWeightedDualWindowBall S N (originalWindowRadius n) ∩
      {q | ε ≤ ‖ψ q‖}
    have hb : IsClosed {q | ε ≤ ‖ψ q‖} := isClosed_le continuous_const hψ.norm
    have hc : ∀ n, IsClosed (B n) := fun n =>
      (originalWeightedDualWindowBall_isClosed S N (originalWindowRadius n)).inter hb
    have hd : ∀ n, B (n + 1) ⊆ B n := by
      intro n q hq
      exact ⟨originalWeightedDualWindowBall_antitone S N
        (originalWindowRadius_strictMono.monotone (Nat.le_succ n)) hq.1, hq.2⟩
    have hn : ∀ n, (B n).Nonempty := by
      intro n
      obtain ⟨q, hq, he⟩ := h n
      exact ⟨q, hq, he⟩
    have hk : IsCompact (B 0) :=
      (originalWeightedDualWindowBall_isCompact S N (originalWindowRadius 0)).inter_right hb
    obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed B hd hn hk hc
    have hw : q ∈ originalWeightedDualSupportedFourierPairBall S N := by
      rw [← originalWeightedDualWindowBall_iInter]
      exact Set.mem_iInter.mpr (fun n => (Set.mem_iInter.mp hq n).1)
    have he : ε ≤ ‖ψ q‖ := (Set.mem_iInter.mp hq 0).2
    rw [hzero q hw, norm_zero] at he
    exact (not_le_of_gt hε) he
  obtain ⟨k, hk⟩ := hsmall
  exact ⟨k, fun R hR q hq => hk q (originalWeightedDualWindowBall_antitone S N hR hq)⟩

/-- A genuine BOTH-record observation of the original full Schwartz distributions. -/
def originalWeightedDualPairObservation (N : ℕ) (a b : SchwartzMap ℝ ℂ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) : ℂ :=
  originalWeightedDualPhysicalDistribution N q a + originalWeightedDualSpectralDistribution N q b

/-- EVERY full paired Schwartz observation is continuous on the actual weak dual. -/
theorem originalWeightedDualPairObservation_continuous (N : ℕ) (a b : SchwartzMap ℝ ℂ) :
    Continuous (originalWeightedDualPairObservation N a b) :=
  (originalWeightedDualPhysicalDistribution_eval_continuous N a).add
    (originalWeightedDualSpectralDistribution_eval_continuous N b)

/-- Actual window membership retains the WHOLE original Fourier equation in the paired observation. -/
theorem originalWeightedDualPairObservation_eq_fourier (S : LocallyFiniteCarrier) (N : ℕ)
    (R : ℝ) (a b : SchwartzMap ℝ ℂ) (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)))
    (hq : q ∈ originalWeightedDualWindowBall S N R) :
    originalWeightedDualPairObservation N a b q =
      originalWeightedDualPhysicalDistribution N q a + 𝓕 (originalWeightedDualPhysicalDistribution N q) b := by
  unfold originalWeightedDualPairObservation
  rw [hq.1.2]

/-- Vanishing on the COMPLETE ORIGINAL prefix unit ball yields a genuine
uniform radius bound on ALL window duals, with BOTH original records retained. -/
theorem originalWeightedDualWindowBall_original_observation_small
    (S : LocallyFiniteCarrier) (N : ℕ) (a b : SchwartzMap ℝ ℂ)
    (hzero : ∀ T ∈ originalStrongPairUnitBall S N, T a + 𝓕 T b = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ R : ℝ, originalWindowRadius k ≤ R →
      ∀ q ∈ originalWeightedDualWindowBall S N R,
        ‖originalWeightedDualPairObservation N a b q‖ < ε := by
  apply originalWeightedDualWindowBall_uniform_small S N _
    (originalWeightedDualPairObservation_continuous N a b) _ ε hε
  intro q hq
  have hT := originalWeightedDualSupportedFourierPairBall_original_strong S N q hq
  unfold originalWeightedDualPairObservation
  rw [hq.1.2]
  exact hzero _ hT

/-- A SINGLE derived window works simultaneously for any finite family
of full BOTH-record observations vanishing on the complete original prefix class. -/
theorem originalWeightedDualWindowBall_finite_original_observations_small
    (S : LocallyFiniteCarrier) (k : ℕ) (N : Fin k → ℕ) (a b : Fin k → SchwartzMap ℝ ℂ)
    (hzero : ∀ i, ∀ T ∈ originalStrongPairUnitBall S (N i), T (a i) + 𝓕 T (b i) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ R : ℝ, originalWindowRadius m ≤ R →
      ∀ i, ∀ q ∈ originalWeightedDualWindowBall S (N i) R,
        ‖originalWeightedDualPairObservation (N i) (a i) (b i) q‖ < ε := by
  classical
  have hi := fun i => originalWeightedDualWindowBall_original_observation_small S (N i) (a i) (b i)
    (hzero i) ε hε
  choose r hr using hi
  refine ⟨Finset.univ.sup r, ?_⟩
  intro R hR i q hq
  apply hr i R _ q hq
  exact (originalWindowRadius_strictMono.monotone (Finset.le_sup (Finset.mem_univ i))).trans hR

/-- The actual radius also controls the SUM of two residual absolute values,
as required by the physical and spectral window estimates in the infinite route. -/
theorem originalWeightedDualWindowBall_two_original_observations_small
    (S : LocallyFiniteCarrier) (N : ℕ) (a b c d : SchwartzMap ℝ ℂ)
    (hz₁ : ∀ T ∈ originalStrongPairUnitBall S N, T a + 𝓕 T b = 0)
    (hz₂ : ∀ T ∈ originalStrongPairUnitBall S N, T c + 𝓕 T d = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ R : ℝ, originalWindowRadius k ≤ R →
      ∀ q ∈ originalWeightedDualWindowBall S N R,
        ‖originalWeightedDualPairObservation N a b q‖ +
          ‖originalWeightedDualPairObservation N c d q‖ < ε := by
  obtain ⟨k₁, hk₁⟩ := originalWeightedDualWindowBall_original_observation_small S N a b hz₁
    (ε / 2) (half_pos hε)
  obtain ⟨k₂, hk₂⟩ := originalWeightedDualWindowBall_original_observation_small S N c d hz₂
    (ε / 2) (half_pos hε)
  refine ⟨max k₁ k₂, ?_⟩
  intro R hR q hq
  have h₁ := hk₁ R ((originalWindowRadius_strictMono.monotone (le_max_left _ _)).trans hR) q hq
  have h₂ := hk₂ R ((originalWindowRadius_strictMono.monotone (le_max_right _ _)).trans hR) q hq
  simpa only [add_halves] using add_lt_add h₁ h₂

/-- BOTH actual original records on ANY locally finite carrier inside the
prefix plus real exterior obey the derived uniform bound at the original exponent.
No later-carrier admissibility or radius certificate is supplied. -/
theorem originalStrongPair_window_observation_small
    (S : LocallyFiniteCarrier) (N : ℕ) (a b : SchwartzMap ℝ ℂ)
    (hzero : ∀ T ∈ originalStrongPairUnitBall S N, T a + 𝓕 T b = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ R : ℝ, originalWindowRadius k ≤ R →
      ∀ (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
        (_hT : T ∈ stronglyTemperedAtomicAtExponent A N)
        (_hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent A N),
        originalStrongPairVariation A N T ≤ 1 →
        A.carrier ⊆ originalExteriorWindow S.carrier R → ‖T a + 𝓕 T b‖ < ε := by
  obtain ⟨k, hk⟩ := originalWeightedDualWindowBall_original_observation_small S N a b hzero ε hε
  refine ⟨k, ?_⟩
  intro R hR A T hT hF hu hA
  have hq := originalStrongPairC0Dual_mem_window_ball A S N R T hT hF hu hA
  have h := hk R hR _ hq
  simpa only [originalWeightedDualPairObservation, originalStrongPairC0Dual_physical,
    originalStrongPairC0Dual_spectral] using h

end
end MeyerGeneralProblem
