module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalSeparateLiftOverlaps

@[expose] public section

/-! Genuine global separate-pole polynomial splitting from ALL four actual
chart lifts. The overlap cocycle, regularity and global square bounds are derived
inside this proof. Its actual complete-prefix specialization supplies the local
lifts and original divisor facts internally, without a gluing certificate. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Four local separate-pole lifts produce genuine GLOBAL positive numerators
with the required individual square bounds. Crossings remain allowed: only
relative primality, actual corners and literal chart identities are used. -/
theorem originalPositive_four_chart_global_split (dq de : ℕ)
    (q e r : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hq : OriginalPositiveInSquare q dq) (he : OriginalPositiveInSquare e de)
    (hr : OriginalPositiveInSquare r (dq + de))
    (h0 : q.coeff (0, 0) ≠ 0) (hd : q.coeff (dq, dq) ≠ 0) (hrel : IsRelPrime q e)
    (hlocal : ∀ c : Bool × Bool, ∃ U V : AddMonoidAlgebra ℂ (ℕ × ℕ),
      originalPositiveChartReflection c (dq + de) r =
        originalPositiveChartReflection c de e * U + originalPositiveChartReflection c dq q * V) :
    ∃ U V : AddMonoidAlgebra ℂ (ℕ × ℕ),
      OriginalPositiveInSquare U dq ∧ OriginalPositiveInSquare V de ∧ r = e * U + q * V := by
  classical
  choose U V hUV using hlocal
  let A (c : Bool × Bool) := originalLaurentChartReflection c dq (originalPositiveLaurentEmbedding (U c))
  let B (c : Bool × Bool) := originalLaurentChartReflection c de (originalPositiveLaurentEmbedding (V c))
  let qL := originalPositiveLaurentEmbedding q
  let eL := originalPositiveLaurentEmbedding e
  let rL := originalPositiveLaurentEmbedding r
  have hchart (c : Bool × Bool) : rL = eL * A c + qL * B c :=
    originalPositive_local_split_pullback c dq de q e r (U c) (V c) hq he hr (hUV c)
  have hAb (c : Bool × Bool) : OriginalLaurentChartBound c dq (A c) :=
    originalPositive_local_pullback_bound c dq (U c)
  have hBb (c : Bool × Bool) : OriginalLaurentChartBound c de (B c) :=
    originalPositive_local_pullback_bound c de (V c)
  have hq0 : q ≠ 0 := by
    intro hz
    exact h0 (by simp [hz])
  have hqL : qL ≠ 0 := originalPositiveLaurentEmbedding_ne_zero q hq0
  obtain ⟨Hp, hpq, hpe⟩ := originalLaurent_separate_lifts_difference q e hq0 hrel rL
    (A (false, false)) (B (false, false)) (A (true, false)) (B (true, false))
    (hchart (false, false)) (hchart (true, false))
  obtain ⟨Hm, hmq, hme⟩ := originalLaurent_separate_lifts_difference q e hq0 hrel rL
    (A (false, true)) (B (false, true)) (A (true, true)) (B (true, true))
    (hchart (false, true)) (hchart (true, true))
  obtain ⟨Vp, vpq, vpe⟩ := originalLaurent_separate_lifts_difference q e hq0 hrel rL
    (A (false, false)) (B (false, false)) (A (false, true)) (B (false, true))
    (hchart (false, false)) (hchart (false, true))
  obtain ⟨Vm, vmq, vme⟩ := originalLaurent_separate_lifts_difference q e hq0 hrel rL
    (A (true, false)) (B (true, false)) (A (true, true)) (B (true, true))
    (hchart (true, false)) (hchart (true, true))
  have hHp : ∀ n, Hp.coeff n ≠ 0 → 0 ≤ n.2 := by
    intro n hn
    have h := originalLaurent_shared_axis_regular (false, false) (true, false) true dq q hq h0 hd
      _ _ Hp (hAb (false, false)) (hAb (true, false)) rfl hpq n hn
    simpa [originalLaurentAxisIndex] using h
  have hHm : ∀ n, Hm.coeff n ≠ 0 → n.2 ≤ 0 := by
    intro n hn
    have h := originalLaurent_shared_axis_regular (false, true) (true, true) true dq q hq h0 hd
      _ _ Hm (hAb (false, true)) (hAb (true, true)) rfl hmq n hn
    simpa [originalLaurentAxisIndex] using h
  have hVp : ∀ n, Vp.coeff n ≠ 0 → 0 ≤ n.1 := by
    intro n hn
    have h := originalLaurent_shared_axis_regular (false, false) (false, true) false dq q hq h0 hd
      _ _ Vp (hAb (false, false)) (hAb (false, true)) rfl vpq n hn
    simpa [originalLaurentAxisIndex] using h
  have hVm : ∀ n, Vm.coeff n ≠ 0 → n.1 ≤ 0 := by
    intro n hn
    have h := originalLaurent_shared_axis_regular (true, false) (true, true) false dq q hq h0 hd
      _ _ Vm (hAb (true, false)) (hAb (true, true)) rfl vmq n hn
    simpa [originalLaurentAxisIndex] using h
  have hcompat : Hp - Hm = Vp - Vm := by
    apply mul_left_cancel₀ hqL
    linear_combination hpq - hmq - vpq + vmq
  obtain ⟨S, hS, hHpS, hHmS, hVpS, hVmS⟩ :=
    originalLaurent_additive_four_chart_gluing Hp Hm Vp Vm hHp hHm hVp hVm hcompat
  let Ac (c : Bool × Bool) := A c - qL * S c
  let Bc (c : Bool × Bool) := B c + eL * S c
  have hagree (c c' : Bool × Bool) (H : AddMonoidAlgebra ℂ (ℤ × ℤ))
      (hQ : qL * H = A c - A c') (hE : eL * H = B c' - B c)
      (hSS : S c - S c' = H) : Ac c = Ac c' ∧ Bc c = Bc c' := by
    constructor
    · dsimp only [Ac]
      linear_combination -hQ - qL * hSS
    · dsimp only [Bc]
      linear_combination hE + eL * hSS
  have hp := hagree _ _ Hp hpq hpe hHpS
  have hm := hagree _ _ Hm hmq hme hHmS
  have vp := hagree _ _ Vp vpq vpe hVpS
  have vm := hagree _ _ Vm vmq vme hVmS
  have hc (c : Bool × Bool) : Ac c = Ac (false, false) ∧ Bc c = Bc (false, false) := by
    rcases c with ⟨a, b⟩
    cases a <;> cases b
    · exact ⟨rfl, rfl⟩
    · exact ⟨vp.1.symm, vp.2.symm⟩
    · exact ⟨hp.1.symm, hp.2.symm⟩
    · exact ⟨vm.1.symm.trans hp.1.symm, vm.2.symm.trans hp.2.symm⟩
  have hAc (c : Bool × Bool) : OriginalLaurentChartBound c dq (Ac (false, false)) := by
    rw [← (hc c).1]
    exact originalLaurentChartBound_sub c dq _ _ (hAb c)
      (originalLaurentChartBound_mul_regular c dq q hq (S c) (hS c))
  have hBc (c : Bool × Bool) : OriginalLaurentChartBound c de (Bc (false, false)) := by
    rw [← (hc c).2]
    exact originalLaurentChartBound_add c de _ _ (hBb c)
      (originalLaurentChartBound_mul_regular c de e he (S c) (hS c))
  obtain ⟨U', hU', hU'b⟩ := originalLaurent_all_chart_bounds_positive dq (Ac (false, false)) hAc
  obtain ⟨V', hV', hV'b⟩ := originalLaurent_all_chart_bounds_positive de (Bc (false, false)) hBc
  refine ⟨U', V', hU'b, hV'b, ?_⟩
  apply originalPositiveLaurentEmbedding_injective
  have hR : rL = eL * Ac (false, false) + qL * Bc (false, false) := by
    dsimp only [Ac, Bc]
    linear_combination hchart (false, false)
  simpa only [map_add, map_mul, hU', hV'] using hR

end
end MeyerGeneralProblem.StrongParity
