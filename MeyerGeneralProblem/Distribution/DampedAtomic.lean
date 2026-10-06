module

public import MeyerGeneralProblem.Distribution.WeightedAtomic
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

/-! Literal exponential damping of an actual absolutely weighted atomic
record, and its weak limit on every Schwartz test. -/

namespace MeyerGeneralProblem

noncomputable section

open Filter
open scoped Topology

/-- The original symmetric exponential attenuation of a real frequency. -/
def atomicExponentialDamping (x t : ℝ) : ℝ := Real.exp (-2 * Real.pi * |x| * t)

theorem atomicExponentialDamping_pos (x t : ℝ) : 0 < atomicExponentialDamping x t :=
  Real.exp_pos _

theorem atomicExponentialDamping_le_one (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    atomicExponentialDamping x t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hp := mul_nonneg (mul_nonneg Real.pi_pos.le (abs_nonneg x)) ht
  nlinarith

theorem atomicExponentialDamping_norm (x t : ℝ) :
    ‖(atomicExponentialDamping x t : ℂ)‖ = atomicExponentialDamping x t := by
  rw [Complex.norm_real, Real.norm_of_nonneg (atomicExponentialDamping_pos x t).le]

/-- The original damped coefficient family on the entire original carrier. -/
def dampedAtomicCoefficient (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (t : ℝ) (x : S.subtype) : ℂ := (atomicExponentialDamping x t : ℂ) * b x

theorem dampedAtomicCoefficient_weight_summable (S : LocallyFiniteCarrier)
    (b : S.subtype → ℂ) (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N))
    {t : ℝ} (ht : 0 ≤ t) :
    Summable (weightedAtomicMassTerm S (dampedAtomicCoefficient S b t) N) := by
  apply Summable.of_nonneg_of_le (fun x => by unfold weightedAtomicMassTerm; positivity) _ hs
  intro x
  unfold weightedAtomicMassTerm dampedAtomicCoefficient
  rw [norm_mul, atomicExponentialDamping_norm]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_of_le_one_left (norm_nonneg _) (atomicExponentialDamping_le_one x ht)

/-- The actual damped record, with original weighted absolute summability discharged. -/
def dampedAtomicDistribution (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (t : ℝ) (ht : 0 ≤ t) :
    TemperedDistribution ℝ ℂ :=
  weightedAtomicDistribution S (dampedAtomicCoefficient S b t) N
    (dampedAtomicCoefficient_weight_summable S b N hs ht)

theorem dampedAtomicDistribution_apply (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (t : ℝ) (ht : 0 ≤ t)
    (f : SchwartzMap ℝ ℂ) :
    dampedAtomicDistribution S b N hs t ht f =
      ∑' x : S.subtype, dampedAtomicCoefficient S b t x * f x := rfl

/-- The literal damped coefficient sum tends to the complete original record on every
Schwartz test; the summable dominating family is constructed from its original weight. -/
theorem dampedAtomic_sum_tendsto (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun t : ℝ => ∑' x : S.subtype, dampedAtomicCoefficient S b t x * f x)
      (𝓝[>] 0) (𝓝 (weightedAtomicDistribution S b N hs f)) := by
  rw [weightedAtomicDistribution_apply]
  apply tendsto_tsum_of_dominated_convergence (weightedAtomic_samples_summable S b N hs f).norm
  · intro x
    have hc : Continuous (fun t : ℝ => dampedAtomicCoefficient S b t x * f x) := by
      unfold dampedAtomicCoefficient atomicExponentialDamping
      fun_prop
    convert! (hc.tendsto (0 : ℝ)).mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds) using 1
    simp only [dampedAtomicCoefficient, atomicExponentialDamping, mul_zero,
      Real.exp_zero, Complex.ofReal_one, one_mul]
  · filter_upwards [self_mem_nhdsWithin] with t ht x
    unfold dampedAtomicCoefficient
    rw [mul_assoc, norm_mul, atomicExponentialDamping_norm]
    exact mul_le_of_le_one_left (norm_nonneg _) (atomicExponentialDamping_le_one x ht.le)

end

end MeyerGeneralProblem
