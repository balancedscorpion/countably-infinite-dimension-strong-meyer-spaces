module

public import MeyerGeneralProblem.Cardinal.Strong.OrderedArrayUniqueness

@[expose] public section

/-!
# Finite original numerator from the complete two-sided recurrence

Both original half-lines are retained. Their convolution equality confines
the numerator to a half-open slab. Local finiteness gives finite support
without any mass bound, forward construction or separation premise.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The original half-line cut includes the threshold. -/
def arrayPositiveCut (L : G →+ ℝ) (s : ℝ) (u : G → ℂ) (n : G) : ℂ := by
  classical
  exact if s ≤ L n then u n else 0

/-- The other original half-line excludes the threshold. -/
def arrayNegativeCut (L : G →+ ℝ) (s : ℝ) (u : G → ℂ) (n : G) : ℂ := by
  classical
  exact if L n < s then u n else 0

theorem arrayCuts_add (L : G →+ ℝ) (s : ℝ) (u : G → ℂ) :
    arrayPositiveCut L s u + arrayNegativeCut L s u = u := by
  classical
  funext n
  by_cases h : s ≤ L n <;> simp [arrayPositiveCut, arrayNegativeCut, h, not_lt.mpr]

theorem annihilatorArrayConvolution_add (p : G →₀ ℂ) (u v : G → ℂ) (n : G) :
    annihilatorArrayConvolution p (u + v) n =
      annihilatorArrayConvolution p u n + annihilatorArrayConvolution p v n := by
  simp only [annihilatorArrayConvolution, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem annihilatorArrayConvolution_sub (p : G →₀ ℂ) (u v : G → ℂ) (n : G) :
    annihilatorArrayConvolution p (u - v) n =
      annihilatorArrayConvolution p u n - annihilatorArrayConvolution p v n := by
  simp only [annihilatorArrayConvolution, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The numerator is the literal finite convolution of the original positive cut. -/
def cutArrayNumerator (L : G →+ ℝ) (p : G →₀ ℂ) (s : ℝ) (u : G → ℂ) : G → ℂ :=
  annihilatorArrayConvolution p (arrayPositiveCut L s u)

theorem cutArrayNumerator_eq_negative (L : G →+ ℝ) (p : G →₀ ℂ)
    (s : ℝ) (u : G → ℂ) (hconv : ∀ n, annihilatorArrayConvolution p u n = 0) (n : G) :
    cutArrayNumerator L p s u n = -annihilatorArrayConvolution p (arrayNegativeCut L s u) n := by
  have h := hconv n
  rw [← arrayCuts_add L s u, annihilatorArrayConvolution_add] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The exact slab endpoints come from both original half-lines. -/
theorem cutArrayNumerator_support_slab (L : G →+ ℝ) (p : G →₀ ℂ)
    (s lo hi : ℝ) (hlo : ∀ m ∈ p.support, lo ≤ L m)
    (hhi : ∀ m ∈ p.support, L m ≤ hi) (u : G → ℂ)
    (hconv : ∀ n, annihilatorArrayConvolution p u n = 0) {n : G}
    (hn : cutArrayNumerator L p s u n ≠ 0) : lo + s ≤ L n ∧ L n < hi + s := by
  classical
  constructor
  · by_contra h
    apply hn
    unfold cutArrayNumerator annihilatorArrayConvolution
    apply Finset.sum_eq_zero
    intro m hm
    have hcut : ¬s ≤ L (n - m) := by
      rw [map_sub]
      linarith [hlo m hm]
    simp only [arrayPositiveCut, ite_eq_right hcut, mul_zero]
  · by_contra h
    apply hn
    rw [cutArrayNumerator_eq_negative L p s u hconv]
    unfold annihilatorArrayConvolution
    rw [Finset.sum_eq_zero]
    · exact neg_zero
    · intro m hm
      have hcut : ¬L (n - m) < s := by
        rw [map_sub]
        linarith [hhi m hm]
      simp only [arrayNegativeCut, ite_eq_right hcut, mul_zero]

/-- A bounded original spectral window contains every source coefficient
used by any nonzero numerator coefficient. -/
theorem cutArrayNumerator_support_finite (L : G →+ ℝ) (p : G →₀ ℂ)
    (s lo hi : ℝ) (hlo : ∀ m ∈ p.support, lo ≤ L m)
    (hhi : ∀ m ∈ p.support, L m ≤ hi) (u : G → ℂ)
    (hu : FrequencyLocallyFinite L u)
    (hconv : ∀ n, annihilatorArrayConvolution p u n = 0) :
    (Function.support (cutArrayNumerator L p s u)).Finite := by
  classical
  let E : Set G := {n | u n ≠ 0 ∧ L n ∈ Set.Icc s (s + hi - lo)}
  have hE : E.Finite := hu s (s + hi - lo)
  apply ((p.support.finite_toSet).biUnion
    (fun m _ => hE.image (fun b => m + b))).subset
  intro n hn
  obtain ⟨m, hm, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hcut : arrayPositiveCut L s u (n - m) ≠ 0 :=
    (mul_ne_zero_iff.mp hterm).2
  have hge : s ≤ L (n - m) := by
    by_contra h
    exact hcut (by dsimp only [arrayPositiveCut]; rw [ite_eq_right h])
  have hun : u (n - m) ≠ 0 := by
    simpa only [arrayPositiveCut, ite_eq_left hge] using hcut
  have hbound := cutArrayNumerator_support_slab L p s lo hi hlo hhi u hconv hn
  refine Set.mem_biUnion hm ?_
  refine ⟨n - m, ⟨hun, hge, ?_⟩, by simp⟩
  rw [map_sub]
  linarith [hlo m hm]

/-- The actual finite Laurent numerator, with finiteness proved from the
original recurrence and original locally finite support. -/
def finiteCutNumerator (L : G →+ ℝ) (p : G →₀ ℂ)
    (s lo hi : ℝ) (hlo : ∀ m ∈ p.support, lo ≤ L m)
    (hhi : ∀ m ∈ p.support, L m ≤ hi) (u : G → ℂ)
    (hu : FrequencyLocallyFinite L u)
    (hconv : ∀ n, annihilatorArrayConvolution p u n = 0) : G →₀ ℂ :=
  Finsupp.ofSupportFinite (cutArrayNumerator L p s u)
    (cutArrayNumerator_support_finite L p s lo hi hlo hhi u hu hconv)

theorem finiteCutNumerator_apply (L : G →+ ℝ) (p : G →₀ ℂ)
    (s lo hi : ℝ) (hlo : ∀ m ∈ p.support, lo ≤ L m)
    (hhi : ∀ m ∈ p.support, L m ≤ hi) (u : G → ℂ)
    (hu : FrequencyLocallyFinite L u)
    (hconv : ∀ n, annihilatorArrayConvolution p u n = 0) (n : G) :
    finiteCutNumerator L p s lo hi hlo hhi u hu hconv n = cutArrayNumerator L p s u n := rfl

end

end MeyerGeneralProblem
