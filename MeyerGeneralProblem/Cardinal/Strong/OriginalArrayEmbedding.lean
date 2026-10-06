module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalNativeSlabs

@[expose] public section

/-! Exact zero extension of WHOLE native arrays along an injective additive
embedding. Finite convolution and BOTH cuts commute with the actual embedding;
all labels outside its image are retained as genuine zero equations. -/
namespace MeyerGeneralProblem
noncomputable section
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- Whole original array embedded at its literal labels and zero elsewhere. -/
def originalArrayEmbedding (e : G →+ H) (u : G → ℂ) (n : H) : ℂ := by
  classical
  exact if h : n ∈ Set.range e then u (Classical.choose h) else 0

/-- Every original label retains exactly its coefficient. -/
theorem originalArrayEmbedding_apply (e : G →+ H) (he : Function.Injective e)
    (u : G → ℂ) (n : G) : originalArrayEmbedding e u (e n) = u n := by
  classical
  rw [originalArrayEmbedding, dite_eq_left (show e n ∈ Set.range e from ⟨n, rfl⟩)]
  congr 1
  exact he (Classical.choose_spec (show e n ∈ Set.range e from ⟨n, rfl⟩))

/-- EVERY exterior label is an actual zero entry. -/
theorem originalArrayEmbedding_zero_off_range (e : G →+ H) (u : G → ℂ)
    (n : H) (hn : n ∉ Set.range e) : originalArrayEmbedding e u n = 0 := by
  classical
  exact dite_eq_right hn

/-- The whole original zero array remains zero. -/
theorem originalArrayEmbedding_zero (e : G →+ H) :
    originalArrayEmbedding e (0 : G → ℂ) = 0 := by
  classical
  funext n
  simp [originalArrayEmbedding]

/-- Additive collisions in whole arrays are retained exactly. -/
theorem originalArrayEmbedding_add (e : G →+ H) (u v : G → ℂ) :
    originalArrayEmbedding e (u + v) = originalArrayEmbedding e u + originalArrayEmbedding e v := by
  classical
  funext n
  by_cases hn : n ∈ Set.range e <;> simp [originalArrayEmbedding, hn]

/-- Scalar multiplication commutes with the full zero extension. -/
theorem originalArrayEmbedding_smul (e : G →+ H) (c : ℂ) (u : G → ℂ) :
    originalArrayEmbedding e (c • u) = c • originalArrayEmbedding e u := by
  classical
  funext n
  by_cases hn : n ∈ Set.range e <;> simp [originalArrayEmbedding, hn]

/-- A finite coefficient array agrees with its genuine finite pushforward. -/
theorem originalArrayEmbedding_finite (e : G →+ H) (he : Function.Injective e)
    (p : G →₀ ℂ) : originalArrayEmbedding e (fun n => p n) = fun n => p.mapDomain e n := by
  classical
  funext n
  by_cases hn : n ∈ Set.range e
  · obtain ⟨m, rfl⟩ := hn
    rw [originalArrayEmbedding_apply e he, Finsupp.mapDomain_apply_of_injective he]
  · rw [originalArrayEmbedding_zero_off_range e _ n hn, Finsupp.mapDomain_of_notMem_range _ _ hn]

/-- Finite convolution commutes with the actual embedding on EVERY label,
including every exterior equation. No convergence or finite-array premise. -/
theorem originalArrayEmbedding_convolution (e : G →+ H) (he : Function.Injective e)
    (p : G →₀ ℂ) (u : G → ℂ) :
    annihilatorArrayConvolution (p.mapDomain e) (originalArrayEmbedding e u) =
      originalArrayEmbedding e (annihilatorArrayConvolution p u) := by
  classical
  funext n
  change (p.mapDomain e).sum (fun m c => c * originalArrayEmbedding e u (n - m)) = _
  rw [Finsupp.sum_mapDomain_index_inj he]
  by_cases hn : n ∈ Set.range e
  · obtain ⟨w, rfl⟩ := hn
    rw [originalArrayEmbedding_apply e he]
    change p.sum (fun m c => c * originalArrayEmbedding e u (e w - e m)) =
      p.sum (fun m c => c * u (w - m))
    apply Finsupp.sum_congr
    intro m _
    rw [← map_sub, originalArrayEmbedding_apply e he]
  · rw [originalArrayEmbedding_zero_off_range e _ n hn]
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro m _
    have hnot : n - e m ∉ Set.range e := by
      rintro ⟨w, hw⟩
      apply hn
      refine ⟨w + m, ?_⟩
      rw [map_add, hw, sub_add_cancel]
    change p m * originalArrayEmbedding e u (n - e m) = 0
    rw [originalArrayEmbedding_zero_off_range e _ _ hnot, mul_zero]

/-- A positive original cut commutes with a frequency-preserving embedding. -/
theorem originalArrayEmbedding_positiveCut (e : G →+ H) (he : Function.Injective e)
    (L : G →+ ℝ) (K : H →+ ℝ) (hfreq : ∀ n, K (e n) = L n)
    (u : G → ℂ) (s : ℝ) :
    arrayPositiveCut K s (originalArrayEmbedding e u) =
      originalArrayEmbedding e (arrayPositiveCut L s u) := by
  classical
  funext n
  by_cases hn : n ∈ Set.range e
  · obtain ⟨m, rfl⟩ := hn
    rw [originalArrayEmbedding_apply e he]
    simp only [arrayPositiveCut, hfreq, originalArrayEmbedding_apply e he]
  · rw [originalArrayEmbedding_zero_off_range e _ n hn]
    simp only [arrayPositiveCut, originalArrayEmbedding_zero_off_range e _ n hn, ite_self]

/-- The strict negative original cut also commutes, retaining zero once. -/
theorem originalArrayEmbedding_negativeCut (e : G →+ H) (he : Function.Injective e)
    (L : G →+ ℝ) (K : H →+ ℝ) (hfreq : ∀ n, K (e n) = L n)
    (u : G → ℂ) (s : ℝ) :
    arrayNegativeCut K s (originalArrayEmbedding e u) =
      originalArrayEmbedding e (arrayNegativeCut L s u) := by
  classical
  funext n
  by_cases hn : n ∈ Set.range e
  · obtain ⟨m, rfl⟩ := hn
    rw [originalArrayEmbedding_apply e he]
    simp only [arrayNegativeCut, hfreq, originalArrayEmbedding_apply e he]
  · rw [originalArrayEmbedding_zero_off_range e _ n hn]
    simp only [arrayNegativeCut, originalArrayEmbedding_zero_off_range e _ n hn, ite_self]

/-- Every original positive cut numerator embeds literally, on the WHOLE group. -/
theorem originalArrayEmbedding_cutNumerator (e : G →+ H) (he : Function.Injective e)
    (L : G →+ ℝ) (K : H →+ ℝ) (hfreq : ∀ n, K (e n) = L n)
    (p : G →₀ ℂ) (u : G → ℂ) (s : ℝ) :
    cutArrayNumerator K (p.mapDomain e) s (originalArrayEmbedding e u) =
      originalArrayEmbedding e (cutArrayNumerator L p s u) := by
  rw [cutArrayNumerator, originalArrayEmbedding_positiveCut e he L K hfreq]
  exact originalArrayEmbedding_convolution e he p (arrayPositiveCut L s u)

end
end MeyerGeneralProblem
