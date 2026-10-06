module

public import MeyerGeneralProblem.Distribution.CompactSmoothDivision
public import MeyerGeneralProblem.Distribution.FiniteAnnihilator
public import MeyerGeneralProblem.Distribution.StrongFiniteSymbolProducts
public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity

@[expose] public section

/-! Genuine value-only atomic recovery from an ACTUAL zero finite annihilator.
Compact smooth division discharges every vanishing test. No incoming source
atomicity, reciprocal-node estimate or Fourier restriction premise is assumed. -/
namespace MeyerGeneralProblem
noncomputable section
open Filter
open scoped Topology ContDiff

/-- Smoothness of the literal finite positive Fourier symbol at every order. -/
theorem finitePositiveExponentialSymbol_contDiff {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) : ContDiff ℝ ∞ (finitePositiveExponentialSymbol a c) := by
  unfold finitePositiveExponentialSymbol
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_combModulationCharacter _ _)

/-- A genuine zero finite annihilator with simple real roots recovers the whole
value-only atomic source on its actual locally finite root carrier. -/
theorem atomicOnCarrier_of_zero_simple_finiteExponentialMultiplication
    {ι : Type*} [Fintype ι] (R : LocallyFiniteCarrier) (a : ι → ℝ) (c : ι → ℂ)
    (hroots : ∀ x, finitePositiveExponentialSymbol a c x = 0 → x ∈ R.carrier)
    (hsimple : ∀ x, finitePositiveExponentialSymbol a c x = 0 →
      deriv (finitePositiveExponentialSymbol a c) x ≠ 0)
    (T : TemperedDistribution ℝ ℂ) (hzero : finiteExponentialMultiplication a c T = 0) :
    AtomicOnCarrier R T := by
  intro f hf
  have hc (g : SchwartzMap ℝ ℂ) (hg : HasCompactSupport g)
      (hgv : SchwartzVanishesOn R g) : T g = 0 := by
    have hz : ∀ x, finitePositiveExponentialSymbol a c x = 0 → g x = 0 :=
      fun x hx => hgv x (hroots x hx)
    let ψ := compactSchwartzDivision g hg (finitePositiveExponentialSymbol a c)
      (finitePositiveExponentialSymbol_contDiff a c) hsimple hz
    have he : finiteCombSchwartzSymbol (fun i => -a i) c ψ = g := by
      ext x
      rw [finiteCombSchwartzSymbol_apply]
      simp only [finiteCombFourierSymbol, neg_neg]
      exact mul_removableQuotient hz x
    have ht := congrArg (fun U : TemperedDistribution ℝ ℂ => U ψ) hzero
    rw [finiteExponentialMultiplication_apply, he] at ht
    simpa using ht
  have hz (N : ℕ) : T (compactSchwartzApproximation N f) = 0 :=
    hc _ (compactSchwartzApproximation_hasCompactSupport N f)
      (compactSchwartzApproximation_preserves_vanishing R N f hf)
  have hl : Tendsto (fun N => T (compactSchwartzApproximation N f)) atTop (𝓝 (T f)) :=
    (T.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have h0 : Tendsto (fun N => T (compactSchwartzApproximation N f)) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hl h0

end
end MeyerGeneralProblem
