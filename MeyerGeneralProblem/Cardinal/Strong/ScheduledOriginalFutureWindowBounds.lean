module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalAnchorStability

@[expose] public section

/-! One actual residual radius works for ALL continuations of a fixed finite
window history. No future-source or future-projection equality is an input. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The radius derived from one finite prefix controls BOTH residual records
for EVERY future continuation sharing that prefix. -/
theorem originalScheduledResidual_all_continuations_small (bound : ℕ → ℕ) (k N : ℕ)
    (hNk : N + 1 ≤ k) (f : SchwartzMap ℝ ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ bound' : ℕ → ℕ, (∀ j < k, bound j = bound' j) →
      ∀ R : ℝ, originalWindowRadius m ≤ R →
      ∀ (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
        (_hT : T ∈ stronglyTemperedAtomicAtExponent A N)
        (_hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent A N),
        originalStrongPairVariation A N T ≤ 1 →
        A.carrier ⊆ originalExteriorWindow (originalScheduledPrefixCarrier bound' k).carrier R →
          ‖(T - originalScheduledAnchorProjection bound' (N + 1) T) f‖ +
            ‖𝓕 (T - originalScheduledAnchorProjection bound' (N + 1) T) f‖ < ε := by
  obtain ⟨m, hm⟩ := originalScheduledResidual_both_window_small bound k N f ε hε
  refine ⟨m, ?_⟩
  intro bound' hb R hR A T hT hF hu hA
  rw [← originalScheduledPrefixCarrier_prefix_congr bound bound' k hb] at hA
  rw [← originalScheduledAnchorProjection_prefix_congr bound bound' (N + 1)
    (fun j hj => hb j (hj.trans_le hNk))]
  exact hm R hR A T hT hF hu hA

/-- A SINGLE radius handles a finite family of exponents and full Schwartz
observations simultaneously for EVERY future continuation of the history. -/
theorem originalScheduledResidual_finite_all_continuations_small (bound : ℕ → ℕ)
    (k d : ℕ) (N : Fin d → ℕ) (hNk : ∀ i, N i + 1 ≤ k) (f : Fin d → SchwartzMap ℝ ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ bound' : ℕ → ℕ, (∀ j < k, bound j = bound' j) →
      ∀ R : ℝ, originalWindowRadius m ≤ R → ∀ i : Fin d,
      ∀ (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
        (_hT : T ∈ stronglyTemperedAtomicAtExponent A (N i))
        (_hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent A (N i)),
        originalStrongPairVariation A (N i) T ≤ 1 →
        A.carrier ⊆ originalExteriorWindow (originalScheduledPrefixCarrier bound' k).carrier R →
          ‖(T - originalScheduledAnchorProjection bound' (N i + 1) T) (f i)‖ +
            ‖𝓕 (T - originalScheduledAnchorProjection bound' (N i + 1) T) (f i)‖ < ε := by
  classical
  have hi := fun i => originalScheduledResidual_all_continuations_small bound k (N i) (hNk i)
    (f i) ε hε
  choose m hm using hi
  refine ⟨Finset.univ.sup m, ?_⟩
  intro bound' hb R hR i A T hT hF hu hA
  exact hm i bound' hb R
    ((originalWindowRadius_strictMono.monotone (Finset.le_sup (Finset.mem_univ i))).trans hR)
    A T hT hF hu hA

/-- Actual future block escape puts the ENTIRE common carrier in the prefix
plus FULL real exterior, including all shared coarse and zero-mass points. -/
theorem originalScheduledCommonCarrier_subset_window (bound : ℕ → ℕ) (k : ℕ) (R : ℝ)
    (hfuture : ∀ n, k ≤ n → R ≤ (originalCommonWindowBounds bound n : ℝ)) :
    (originalScheduledCommonCarrier bound).carrier ⊆
      originalExteriorWindow (originalScheduledPrefixCarrier (originalCommonWindowBounds bound) k).carrier R := by
  intro x hx
  rw [originalScheduledCommonCarrier_carrier] at hx
  rcases hx with hx | hx
  · exact Or.inl (Or.inl hx)
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    by_cases hnk : n < k
    · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨n, hnk⟩, hn⟩))
    · have hR := hfuture n (Nat.le_of_not_gt hnk)
      rcases hn with hp | hs
      · have he := originalScheduledFullPhysicalCarrier_escape _ _
          (originalScheduledPrivatePhysicalCarrier_subset_full _ _ hp)
        exact Or.inr (show R ≤ |x| by linarith)
      · by_cases hc : x ∈ originalSharedCoarseCone.carrier
        · exact Or.inl (Or.inl hc)
        · have he := originalScheduledPrivateSpectralCarrier_noncoarse_escape
            (originalCommonWindowBounds bound) n ⟨hs, hc⟩
          exact Or.inr (show R ≤ |x| by linarith)

/-- One prefix-derived radius controls BOTH records of the ACTUAL infinite common
carrier for every compatible continuation whose future bounds protect that radius.
No source, projection, window-membership or exhaustion certificate is supplied. -/
theorem originalScheduledCommonCarrier_residual_all_continuations_small
    (bound : ℕ → ℕ) (k N : ℕ) (hNk : N + 1 ≤ k)
    (f : SchwartzMap ℝ ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ bound' : ℕ → ℕ, (∀ j < k, bound j = bound' j) →
      ∀ R : ℝ, originalWindowRadius m ≤ R →
      (∀ n, k ≤ n → R ≤ (bound' n : ℝ)) →
      ∀ (T : TemperedDistribution ℝ ℂ),
        T ∈ originalStrongPairUnitBall (originalScheduledCommonCarrier bound') N →
          ‖(T - originalScheduledAnchorProjection (originalCommonWindowBounds bound') (N + 1) T) f‖ +
            ‖𝓕 (T - originalScheduledAnchorProjection (originalCommonWindowBounds bound') (N + 1) T) f‖ < ε := by
  obtain ⟨m, hm⟩ := originalScheduledResidual_all_continuations_small
    (originalCommonWindowBounds bound) k N hNk f ε hε
  refine ⟨m, ?_⟩
  intro bound' hb R hR hfuture T hT
  have hb' : ∀ j < k, originalCommonWindowBounds bound j = originalCommonWindowBounds bound' j := by
    intro j hj
    simp only [originalCommonWindowBounds, hb j hj]
  apply hm (originalCommonWindowBounds bound') hb' R hR (originalScheduledCommonCarrier bound')
    T hT.1 hT.2.1 hT.2.2
  apply originalScheduledCommonCarrier_subset_window
  intro n hn
  exact (hfuture n hn).trans (by exact_mod_cast le_max_left (bound' n) n)

end
end MeyerGeneralProblem.StrongParity
