module

public import MeyerGeneralProblem.Cardinal.Strong.AnnihilatorArrays
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.Finset.Max

@[expose] public section

/-! Ordered uniqueness for locally finite original frequency arrays.
The minimum is obtained from an actual finite bounded window. -/

namespace MeyerGeneralProblem

noncomputable section

variable {G : Type*} [AddCommGroup G]

theorem frequencyLocallyFinite_exists_min (L : G →+ ℝ) (u : G → ℂ)
    (hu : FrequencyLocallyFinite L u) (hlo : ∃ a, ∀ n, u n ≠ 0 → a ≤ L n)
    (hne : ∃ n, u n ≠ 0) :
    ∃ n, u n ≠ 0 ∧ ∀ m, u m ≠ 0 → L n ≤ L m := by
  obtain ⟨a, ha⟩ := hlo
  obtain ⟨n₀, hn₀⟩ := hne
  let E : Set G := {n | u n ≠ 0 ∧ L n ∈ Set.Icc a (L n₀)}
  obtain ⟨n, hn, hmin⟩ := Set.exists_min_image E L (hu a (L n₀))
    ⟨n₀, hn₀, ha n₀ hn₀, le_rfl⟩
  refine ⟨n, hn.1, fun m hm => ?_⟩
  by_cases h : L m ≤ L n₀
  · exact hmin m ⟨hm, ha m hm, h⟩
  · exact hn.2.2.trans (le_of_not_ge h)

/-- A nonzero extreme coefficient cannot annihilate a nonzero array whose
frequency support is locally finite and bounded below. -/
theorem annihilatorArray_eq_zero_of_bounded_below (L : G →+ ℝ)
    (p : G →₀ ℂ) (m₀ : G) (hm₀ : p m₀ ≠ 0)
    (hmin : ∀ m ∈ p.support, m ≠ m₀ → L m₀ < L m)
    (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (hlo : ∃ a, ∀ n, u n ≠ 0 → a ≤ L n)
    (hconv : ∀ n, annihilatorArrayConvolution p u n = 0) : u = 0 := by
  classical
  by_contra hne
  have hsome : ∃ n, u n ≠ 0 := by
    by_contra h
    apply hne
    funext n
    simpa using not_exists.mp h n
  obtain ⟨n, hn, hleast⟩ := frequencyLocallyFinite_exists_min L u hu hlo hsome
  have hterm : annihilatorArrayConvolution p u (m₀ + n) = p m₀ * u n := by
    unfold annihilatorArrayConvolution
    rw [Finset.sum_eq_single m₀]
    · simp only [add_sub_cancel_left]
    · intro m hm hne
      have hz : u (m₀ + n - m) = 0 := by
        by_contra hz
        have h := hleast _ hz
        have he := hmin m hm hne
        simp only [map_sub, map_add] at h
        linarith
      rw [hz, mul_zero]
    · exact fun h => (h (Finsupp.mem_support_iff.mpr hm₀)).elim
  have h := hconv (m₀ + n)
  rw [hterm] at h
  exact (mul_ne_zero hm₀ hn) h

/-- The upper-frequency counterpart is the same proven extremal argument
applied to the actual negated frequency map. -/
theorem annihilatorArray_eq_zero_of_bounded_above (L : G →+ ℝ)
    (p : G →₀ ℂ) (m₁ : G) (hm₁ : p m₁ ≠ 0)
    (hmax : ∀ m ∈ p.support, m ≠ m₁ → L m < L m₁)
    (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (hhi : ∃ b, ∀ n, u n ≠ 0 → L n ≤ b)
    (hconv : ∀ n, annihilatorArrayConvolution p u n = 0) : u = 0 := by
  apply annihilatorArray_eq_zero_of_bounded_below (-L) p m₁ hm₁
  · intro m hm hne
    simpa only [AddMonoidHom.neg_apply, neg_lt_neg_iff] using hmax m hm hne
  · intro a b
    apply (hu (-b) (-a)).subset
    intro n hn
    simp only [AddMonoidHom.neg_apply, Set.mem_Icc] at hn ⊢
    exact ⟨hn.1, by linarith [hn.2.2], by linarith [hn.2.1]⟩
  · obtain ⟨b, hb⟩ := hhi
    refine ⟨-b, fun n hn => ?_⟩
    simpa only [AddMonoidHom.neg_apply, neg_le_neg_iff] using hb n hn
  · exact hconv

end

end MeyerGeneralProblem
