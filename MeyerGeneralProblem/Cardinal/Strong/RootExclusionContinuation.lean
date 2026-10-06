module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalRootImplicit
public import Mathlib.Analysis.Analytic.IsolatedZeros

@[expose] public section

/-! Actual analytic continuation from original compact root labels to the zero endpoint. -/

namespace MeyerGeneralProblem.StrongParity

open Filter Set
open scoped Topology

noncomputable section

/-- Continuity at zero and actual analytic continuation forbid local identity with a wrong base value. -/
theorem analytic_compact_not_eventually_constant {f : ℝ → ℝ} {gamma a : ℝ}
    (hf : AnalyticOnNhd ℝ f (Ioo 0 (1 / 2)))
    (hc : ContinuousWithinAt f (Icc 0 (1 / 2)) 0)
    (hzero : f 0 ≠ gamma) (ha : a ∈ Ioo 0 (1 / 2)) :
    ¬f =ᶠ[𝓝 a] (fun _ => gamma) := by
  intro heq
  have hall : EqOn f (fun _ => gamma) (Ioo 0 (1 / 2)) :=
    hf.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
      isPreconnected_Ioo ha heq
  have hlim : Tendsto f (𝓝[Ioo 0 (1 / 2)] 0) (𝓝 (f 0)) :=
    (hc.mono Ioo_subset_Icc_self).tendsto
  have hevent : f =ᶠ[𝓝[Ioo 0 (1 / 2)] 0] (fun _ => gamma) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hall hx
  have hlim' : Tendsto f (𝓝[Ioo 0 (1 / 2)] 0) (𝓝 gamma) :=
    tendsto_const_nhds.congr' hevent.symm
  have hcl : (0 : ℝ) ∈ closure (Ioo 0 (1 / 2)) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2)]
    norm_num
  have : NeBot (𝓝[Ioo (0 : ℝ) (1 / 2)] 0) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  exact hzero (tendsto_nhds_unique hlim hlim')

/-- A nonzero boundary value excludes accumulating zeros anywhere in the actual slot corridor. -/
theorem analytic_compact_eventually_ne {f : ℝ → ℝ} {gamma a : ℝ}
    (hf : AnalyticOnNhd ℝ f (Ioo 0 (1 / 2)))
    (hc : ContinuousWithinAt f (Icc 0 (1 / 2)) 0)
    (hzero : f 0 ≠ gamma) (ha : a ∈ Ioo 0 (1 / 2)) :
    ∀ᶠ b in 𝓝[≠] a, f b ≠ gamma := by
  have hnot := analytic_compact_not_eventually_constant hf hc hzero ha
  exact ((hf a ha).eventually_eq_or_eventually_ne (analyticAt_const :
    AnalyticAt ℝ (fun _ : ℝ => gamma) a)).resolve_left hnot

/-- Actual injectivity on the original compact domain also excludes every local constant germ. -/
theorem injOn_compact_not_eventually_constant {f : ℝ → ℝ} {gamma a : ℝ}
    (hinj : InjOn f (Icc 0 (1 / 2))) (ha : a ∈ Ioo 0 (1 / 2)) :
    ¬f =ᶠ[𝓝 a] (fun _ => gamma) := by
  intro heq
  have hbase : f a = gamma := heq.self_of_nhds
  have hdomain : ∀ᶠ b in 𝓝 a, b ∈ Icc 0 (1 / 2) := Icc_mem_nhds ha.1 ha.2
  have : NeBot (𝓝[≠] a) := inferInstance
  have heq' : ∀ᶠ b in 𝓝[≠] a, f b = gamma := heq.filter_mono nhdsWithin_le_nhds
  have hdomain' : ∀ᶠ b in 𝓝[≠] a, b ∈ Icc 0 (1 / 2) :=
    hdomain.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ b in 𝓝[≠] a, b ≠ a := by
    exact Filter.Eventually.mono
      (self_mem_nhdsWithin : ∀ᶠ b : ℝ in 𝓝[≠] a, b ∈ ({a}ᶜ : Set ℝ))
      (fun _ hb => by simpa only [mem_compl_iff, mem_singleton_iff] using hb)
  obtain ⟨b, hb, hbdom, hbne⟩ := (heq'.and (hdomain'.and hne)).exists
  exact hbne (hinj hbdom ⟨ha.1.le, ha.2.le⟩ (hb.trans hbase.symm))

/-- An actual analytic and injective compact function has isolated level sets. -/
theorem analytic_injOn_compact_eventually_ne {f : ℝ → ℝ} {gamma a : ℝ}
    (hf : AnalyticOnNhd ℝ f (Ioo 0 (1 / 2)))
    (hinj : InjOn f (Icc 0 (1 / 2))) (ha : a ∈ Ioo 0 (1 / 2)) :
    ∀ᶠ b in 𝓝[≠] a, f b ≠ gamma := by
  exact ((hf a ha).eventually_eq_or_eventually_ne (analyticAt_const :
    AnalyticAt ℝ (fun _ : ℝ => gamma) a)).resolve_left
      (injOn_compact_not_eventually_constant hinj ha)

end

end MeyerGeneralProblem.StrongParity
