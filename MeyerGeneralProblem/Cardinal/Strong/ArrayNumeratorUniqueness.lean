module

public import MeyerGeneralProblem.Cardinal.Strong.FiniteArrayNumerator

@[expose] public section

/-! The finite original cut numerator determines the COMPLETE two-sided array.
This uses the two extremal uniqueness arguments, with both original cuts. -/

namespace MeyerGeneralProblem

noncomputable section

variable {G : Type*} [AddCommGroup G]

theorem FrequencyLocallyFinite.sub {L : G →+ ℝ} {u v : G → ℂ}
    (hu : FrequencyLocallyFinite L u) (hv : FrequencyLocallyFinite L v) :
    FrequencyLocallyFinite L (u - v) := by
  intro a b
  apply ((hu a b).union (hv a b)).subset
  intro n hn
  by_cases h : u n = 0
  · exact Or.inr ⟨by simpa only [Pi.sub_apply, h, zero_sub, neg_ne_zero] using hn.1, hn.2⟩
  · exact Or.inl ⟨h, hn.2⟩

theorem FrequencyLocallyFinite.positiveCut {L : G →+ ℝ} {u : G → ℂ}
    (hu : FrequencyLocallyFinite L u) (s : ℝ) :
    FrequencyLocallyFinite L (arrayPositiveCut L s u) := by
  classical
  intro a b
  apply (hu a b).subset
  intro n hn
  refine ⟨?_, hn.2⟩
  by_contra h
  exact hn.1 (by simp [arrayPositiveCut, h])

theorem FrequencyLocallyFinite.negativeCut {L : G →+ ℝ} {u : G → ℂ}
    (hu : FrequencyLocallyFinite L u) (s : ℝ) :
    FrequencyLocallyFinite L (arrayNegativeCut L s u) := by
  classical
  intro a b
  apply (hu a b).subset
  intro n hn
  refine ⟨?_, hn.2⟩
  by_contra h
  exact hn.1 (by simp [arrayNegativeCut, h])

/-- Two locally finite arrays with the same convolution and bounded-below
frequency support agree, using the actual nonzero lower extreme of p. -/
theorem annihilatorArray_solution_unique_below (L : G →+ ℝ) (p : G →₀ ℂ)
    (m₀ : G) (hm₀ : p m₀ ≠ 0)
    (hmin : ∀ m ∈ p.support, m ≠ m₀ → L m₀ < L m)
    (u v : G → ℂ) (hu : FrequencyLocallyFinite L u) (hv : FrequencyLocallyFinite L v)
    (hlo : ∃ a, ∀ n, (u - v) n ≠ 0 → a ≤ L n)
    (heq : ∀ n, annihilatorArrayConvolution p u n = annihilatorArrayConvolution p v n) :
    u = v := by
  apply sub_eq_zero.mp
  apply annihilatorArray_eq_zero_of_bounded_below L p m₀ hm₀ hmin (u - v)
    (hu.sub hv) hlo
  intro n
  rw [annihilatorArrayConvolution_sub, heq n, sub_self]

/-- The two original half-line solutions are both unique. Consequently the
finite numerator determines every original array coefficient on both sides. -/
theorem cutArrayNumerator_injective_on_kernel (L : G →+ ℝ) (p : G →₀ ℂ)
    (m₀ m₁ : G) (hm₀ : p m₀ ≠ 0) (hm₁ : p m₁ ≠ 0)
    (hmin : ∀ m ∈ p.support, m ≠ m₀ → L m₀ < L m)
    (hmax : ∀ m ∈ p.support, m ≠ m₁ → L m < L m₁)
    (s : ℝ) (u v : G → ℂ)
    (hu : FrequencyLocallyFinite L u) (hv : FrequencyLocallyFinite L v)
    (hcu : ∀ n, annihilatorArrayConvolution p u n = 0)
    (hcv : ∀ n, annihilatorArrayConvolution p v n = 0)
    (heq : cutArrayNumerator L p s u = cutArrayNumerator L p s v) : u = v := by
  classical
  have hpos : arrayPositiveCut L s u = arrayPositiveCut L s v := by
    apply annihilatorArray_solution_unique_below L p m₀ hm₀ hmin
      _ _ (hu.positiveCut s) (hv.positiveCut s)
    · refine ⟨s, fun n hn => ?_⟩
      by_contra h
      exact hn (by simp [arrayPositiveCut, h])
    · exact congrFun heq
  have hneg : arrayNegativeCut L s u = arrayNegativeCut L s v := by
    apply sub_eq_zero.mp
    apply annihilatorArray_eq_zero_of_bounded_above L p m₁ hm₁ hmax
      _ ((hu.negativeCut s).sub (hv.negativeCut s))
    · refine ⟨s, fun n hn => ?_⟩
      by_contra h
      have hnot : ¬L n < s := by linarith
      exact hn (by simp [arrayNegativeCut, hnot])
    · intro n
      have h := congrFun heq n
      rw [cutArrayNumerator_eq_negative L p s u hcu,
        cutArrayNumerator_eq_negative L p s v hcv] at h
      rw [annihilatorArrayConvolution_sub, neg_inj.mp h, sub_self]
  rw [← arrayCuts_add L s u, ← arrayCuts_add L s v, hpos, hneg]

end

end MeyerGeneralProblem
