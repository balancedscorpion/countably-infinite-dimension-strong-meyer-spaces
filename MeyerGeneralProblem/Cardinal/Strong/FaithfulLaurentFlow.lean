module

public import MeyerGeneralProblem.Cardinal.Strong.ProductAnnihilator
public import MeyerGeneralProblem.Cardinal.Strong.DampedSpectral

@[expose] public section

/-! Actual faithfulness of finite Laurent evaluation on the irrational flow.
The lowest nonzero frequency is recovered by vertical exponential decay. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open Filter
open scoped Topology

theorem complexUnitPhase_vertical_tendsto_zero {v : ℝ} (hv : 0 < v) :
    Tendsto (fun t : ℝ => complexUnitPhase ((v : ℂ) * ((t : ℂ) * Complex.I)))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [complexUnitPhase_vertical_norm]
  have ha : -2 * Real.pi * v < 0 := by nlinarith [Real.pi_pos]
  exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg ha)

theorem rankTwoLaurentEvaluation_eq_sum (p : AddMonoidAlgebra ℂ (ℤ × ℤ)) (z : ℂ) :
    rankTwoLaurentEvaluation z p =
      ∑ n ∈ p.coeff.support, p.coeff n * rankTwoEntireCharacter z (Multiplicative.ofAdd n) := by
  rw [rankTwoLaurentEvaluation, AddMonoidAlgebra.lift_apply']
  simp only [Finsupp.sum, Algebra.algebraMap_self, RingHom.id_apply]

/-- Vanishing on the whole upper half-plane forces EVERY actual Laurent
coefficient to vanish; no equality of sums at a single point is used. -/
theorem rankTwoLaurentEvaluation_zero_iff (p : AddMonoidAlgebra ℂ (ℤ × ℤ)) :
    (∀ z : ℂ, 0 < z.im → rankTwoLaurentEvaluation z p = 0) ↔ p = 0 := by
  classical
  constructor
  · intro hz
    by_contra hp
    have hs : p.coeff.support.Nonempty := by
      apply Finsupp.support_nonempty_iff.mpr
      intro hc
      exact hp (AddMonoidAlgebra.coeff_injective hc)
    obtain ⟨n₀, hn₀, hmin⟩ := p.coeff.support.exists_min_image rankTwoFrequencyHom hs
    have hstrict (n : ℤ × ℤ) (hn : n ∈ p.coeff.support) (hne : n ≠ n₀) :
        0 < rankTwoFrequencyHom (n - n₀) := by
      rw [map_sub, sub_pos]
      exact lt_of_le_of_ne (hmin n hn)
        (fun he => hne (rankTwoFrequencyHom_injective he.symm))
    let f : ℝ → ℂ := fun t => ∑ n ∈ p.coeff.support,
      p.coeff n * complexUnitPhase
        ((rankTwoFrequencyHom (n - n₀) : ℝ) * ((t : ℂ) * Complex.I))
    have hlim : Tendsto f atTop (𝓝 (p.coeff n₀)) := by
      have ht : ∀ n ∈ p.coeff.support, Tendsto
          (fun t : ℝ => p.coeff n * complexUnitPhase
            ((rankTwoFrequencyHom (n - n₀) : ℝ) * ((t : ℂ) * Complex.I)))
          atTop (𝓝 (if n = n₀ then p.coeff n else 0)) := by
        intro n hn
        by_cases he : n = n₀
        · subst n
          simp [complexUnitPhase]
        · simpa only [ite_eq_right he, mul_zero] using
            (complexUnitPhase_vertical_tendsto_zero (hstrict n hn he)).const_mul (p.coeff n)
      simpa only [Finset.sum_ite_eq', ite_eq_left hn₀] using tendsto_finsetSum _ ht
    have heval (t : ℝ) : f t = rankTwoLaurentEvaluation ((t : ℂ) * Complex.I) p *
        rankTwoEntireCharacter ((t : ℂ) * Complex.I) (Multiplicative.ofAdd (-n₀)) := by
      rw [rankTwoLaurentEvaluation_eq_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      rw [mul_assoc]
      change p.coeff n * rankTwoEntireCharacter _ (Multiplicative.ofAdd (n - n₀)) = _
      rw [sub_eq_add_neg]
      exact congrArg (p.coeff n * ·)
        ((rankTwoEntireCharacter _).map_mul (Multiplicative.ofAdd n) (Multiplicative.ofAdd (-n₀)))
    have hzero : ∀ᶠ t : ℝ in atTop, f t = 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [heval t, hz _ (by simpa using ht), zero_mul]
    have hlim0 : Tendsto f atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (hzero.mono fun _ he => he.symm)
    exact (Finsupp.mem_support_iff.mp hn₀) (tendsto_nhds_unique hlim hlim0)
  · intro hp z _
    rw [hp, map_zero]

theorem rankTwoLaurentEvaluation_injective (p q : AddMonoidAlgebra ℂ (ℤ × ℤ))
    (h : ∀ z : ℂ, 0 < z.im → rankTwoLaurentEvaluation z p = rankTwoLaurentEvaluation z q) :
    p = q := by
  apply sub_eq_zero.mp
  apply (rankTwoLaurentEvaluation_zero_iff (p - q)).mp
  intro z hz
  rw [map_sub, h z hz, sub_self]

end

end MeyerGeneralProblem.StrongParity
