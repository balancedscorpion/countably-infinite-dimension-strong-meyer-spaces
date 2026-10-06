module

public import MeyerGeneralProblem.Distribution.MeyerSpace

@[expose] public section

/-!
# Actual atomic distributions from absolute weighted mass summability

A polynomially weighted absolute coefficient sum defines a genuine
continuous Schwartz functional. Its global atomic meaning, local action,
and canonical isolation coefficients are proved from the literal sum.
The constructor has no Fourier-pair hypothesis or conclusion.
-/

namespace MeyerGeneralProblem

noncomputable section

open SchwartzMap
open scoped SchwartzMap

/-- The absolute original coefficient weight on an arbitrary actual carrier. -/
def weightedAtomicMassTerm (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (x : S.subtype) : ℝ := ‖b x‖ / (1 + |(x : ℝ)|) ^ N

theorem weightedAtomic_sample_norm_le (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (f : SchwartzMap ℝ ℂ) (x : S.subtype) :
    ‖b x * f x‖ ≤
      (2 ^ N * (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f) *
        weightedAtomicMassTerm S b N x := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl f (x : ℝ)
  have h' : (1 + |(x : ℝ)|) ^ N * ‖f x‖ ≤
      2 ^ N * (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f := by
    convert! h using 1;
      norm_num [Real.norm_eq_abs, norm_iteratedFDeriv_zero, schwartzSeminormFamily]
  have hpos : 0 < (1 + |(x : ℝ)|) ^ N := by positivity
  have hf : ‖f x‖ ≤
      (2 ^ N * (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f) /
        (1 + |(x : ℝ)|) ^ N := by
    exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using h')
  rw [norm_mul, weightedAtomicMassTerm]
  exact (mul_le_mul_of_nonneg_left hf (norm_nonneg _)).trans_eq (by ring)

theorem weightedAtomic_samples_summable (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (f : SchwartzMap ℝ ℂ) :
    Summable (fun x : S.subtype => b x * f x) := by
  apply Summable.of_norm_bounded (hs.mul_left
    (2 ^ N * (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f))
  exact weightedAtomic_sample_norm_le S b N f

theorem weightedAtomic_sum_norm_le (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (f : SchwartzMap ℝ ℂ) :
    ‖∑' x : S.subtype, b x * f x‖ ≤
      (2 ^ N * ∑' x, weightedAtomicMassTerm S b N x) *
        (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f := by
  have hf := weightedAtomic_samples_summable S b N hs f
  calc
    _ ≤ ∑' x : S.subtype, ‖b x * f x‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' x : S.subtype,
        (2 ^ N * (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f) *
          weightedAtomicMassTerm S b N x :=
      hf.norm.tsum_le_tsum (weightedAtomic_sample_norm_le S b N f) (hs.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

/-- The literal absolutely convergent atomic sum as a continuous Schwartz map. -/
def weightedAtomicCLM (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => ∑' x : S.subtype, b x * f x)
    (fun f g => by
      simp only [add_apply, mul_add]
      exact Summable.tsum_add (weightedAtomic_samples_summable S b N hs f)
        (weightedAtomic_samples_summable S b N hs g))
    (fun c f => by
      simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
      simp_rw [show ∀ x : S.subtype, b x * (c * f x) = c * (b x * f x) by intro x; ring]
      exact tsum_mul_left)
    ⟨Finset.Iic (N, 0), 2 ^ N * ∑' x, weightedAtomicMassTerm S b N x, by
      have ht : 0 ≤ ∑' x, weightedAtomicMassTerm S b N x :=
        tsum_nonneg (fun x => by unfold weightedAtomicMassTerm; positivity)
      positivity, weightedAtomic_sum_norm_le S b N hs⟩

/-- The genuine tempered distribution of an absolutely weighted atomic family. -/
def weightedAtomicDistribution (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) : TemperedDistribution ℝ ℂ :=
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
    (SchwartzMap ℝ ℂ) ℂ (weightedAtomicCLM S b N hs)

theorem weightedAtomicDistribution_apply (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (f : SchwartzMap ℝ ℂ) :
    weightedAtomicDistribution S b N hs f = ∑' x : S.subtype, b x * f x := rfl

theorem weightedAtomicDistribution_atomicOnCarrier (S : LocallyFiniteCarrier)
    (b : S.subtype → ℂ) (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) :
    AtomicOnCarrier S (weightedAtomicDistribution S b N hs) := by
  intro f hf
  rw [weightedAtomicDistribution_apply]
  have hz : (fun x : S.subtype => b x * f x) = fun _ => (0 : ℂ) := by
    funext x
    rw [hf x x.property, mul_zero]
  rw [hz, tsum_zero]

theorem weightedAtomicDistribution_isolation (S : LocallyFiniteCarrier)
    (b : S.subtype → ℂ) (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (x : S.subtype) :
    weightedAtomicDistribution S b N hs (S.isolationSchwartz x) = b x := by
  classical
  rw [weightedAtomicDistribution_apply, tsum_eq_single x]
  · rw [S.isolationSchwartz_self, mul_one]
  · intro y hy
    rw [S.isolationSchwartz_apply_subtype]
    simp [hy]

theorem weightedAtomicDistribution_mem_strongExponent (S : LocallyFiniteCarrier)
    (b : S.subtype → ℂ) (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) :
    weightedAtomicDistribution S b N hs ∈ stronglyTemperedAtomicAtExponent S N := by
  refine ⟨atomicOnCarrier_hasLocallyAtomicAction S _
    (weightedAtomicDistribution_atomicOnCarrier S b N hs), ?_⟩
  change Summable (fun x : S.subtype =>
    ‖weightedAtomicDistribution S b N hs (S.isolationSchwartz x)‖ / (1 + |(x : ℝ)|) ^ N)
  simp_rw [weightedAtomicDistribution_isolation]
  exact hs

theorem weightedAtomicDistribution_isLocallyAtomicCoefficientFamily (S : LocallyFiniteCarrier)
    (b : S.subtype → ℂ) (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) :
    IsLocallyAtomicCoefficientFamily S (weightedAtomicDistribution S b N hs) b := by
  have h := atomicOnCarrier_isLocallyAtomicCoefficientFamily S _
    (weightedAtomicDistribution_atomicOnCarrier S b N hs)
  have hb : (fun x => weightedAtomicDistribution S b N hs (S.isolationSchwartz x)) = b :=
    funext (weightedAtomicDistribution_isolation S b N hs)
  rw [hb] at h
  exact h

end

end MeyerGeneralProblem
