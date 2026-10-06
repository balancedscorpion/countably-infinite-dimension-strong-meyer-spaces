module

public import MeyerGeneralProblem.Distribution.OriginalWeightedSchwartzC0
public import Mathlib.Analysis.Normed.Module.WeakDual

@[expose] public section

/-! Genuine C0 duals of the ORIGINAL weighted atomic coefficient records.
Every coefficient and Schwartz action is literal; the dual norm is bounded by
the SAME original weighted absolute variation, with no measure certificate. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty

/-- The actual original weighted atomic coefficient, at every original carrier point. -/
def originalWeightedC0Coefficient (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (x : S.subtype) : ℂ := b x / (((1 + |(x : ℝ)|) ^ N : ℝ) : ℂ)

/-- Its norm is EXACTLY the original weighted absolute mass term. -/
theorem originalWeightedC0Coefficient_norm (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (x : S.subtype) :
    ‖originalWeightedC0Coefficient S b N x‖ = weightedAtomicMassTerm S b N x := by
  simp only [originalWeightedC0Coefficient, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + |(x : ℝ)|) ^ N), weightedAtomicMassTerm]

/-- EVERY original C0 sample is bounded by the literal original weighted mass. -/
theorem originalWeightedC0_sample_norm_le (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (g : C₀(ℝ, ℂ)) (x : S.subtype) :
    ‖originalWeightedC0Coefficient S b N x * g x‖ ≤ weightedAtomicMassTerm S b N x * ‖g‖ := by
  rw [norm_mul, originalWeightedC0Coefficient_norm]
  have hg : ‖g (x : ℝ)‖ ≤ ‖g‖ := by
    have h := g.toBCF.norm_coe_le_norm (x : ℝ)
    change ‖g (x : ℝ)‖ ≤ ‖g.toBCF‖ at h
    simpa only [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using h
  exact mul_le_mul_of_nonneg_left hg (by unfold weightedAtomicMassTerm; positivity)

/-- The ORIGINAL weighted atomic C0 samples are absolutely summable. -/
theorem originalWeightedC0_samples_summable (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (g : C₀(ℝ, ℂ)) :
    Summable (fun x : S.subtype => originalWeightedC0Coefficient S b N x * g x) :=
  Summable.of_norm_bounded (hs.mul_right ‖g‖) (originalWeightedC0_sample_norm_le S b N g)

/-- Whole C0 action is bounded by the SAME original weighted variation. -/
theorem originalWeightedC0_sum_norm_le (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (g : C₀(ℝ, ℂ)) :
    ‖∑' x : S.subtype, originalWeightedC0Coefficient S b N x * g x‖ ≤
      (∑' x : S.subtype, weightedAtomicMassTerm S b N x) * ‖g‖ := by
  have hg := originalWeightedC0_samples_summable S b N hs g
  calc
    _ ≤ ∑' x : S.subtype, ‖originalWeightedC0Coefficient S b N x * g x‖ := norm_tsum_le_tsum_norm hg.norm
    _ ≤ ∑' x : S.subtype, weightedAtomicMassTerm S b N x * ‖g‖ :=
      hg.norm.tsum_le_tsum (originalWeightedC0_sample_norm_le S b N g) (hs.mul_right ‖g‖)
    _ = _ := tsum_mul_right

/-- The genuine linear C0 action of one full original atomic record. -/
def originalWeightedAtomicC0Linear (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) : C₀(ℝ, ℂ) →ₗ[ℂ] ℂ where
  toFun g := ∑' x : S.subtype, originalWeightedC0Coefficient S b N x * g x
  map_add' f g := by
    simp only [ZeroAtInftyContinuousMap.add_apply, mul_add]
    exact Summable.tsum_add (originalWeightedC0_samples_summable S b N hs f)
      (originalWeightedC0_samples_summable S b N hs g)
  map_smul' c g := by
    simp only [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ x : S.subtype, originalWeightedC0Coefficient S b N x * (c * g x) =
      c * (originalWeightedC0Coefficient S b N x * g x) by intro x; ring]
    exact tsum_mul_left

/-- The FULL original weighted atomic record is an actual continuous C0 dual. -/
def originalWeightedAtomicC0Dual (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) : StrongDual ℂ C₀(ℝ, ℂ) :=
  (originalWeightedAtomicC0Linear S b N hs).mkContinuous
    (∑' x : S.subtype, weightedAtomicMassTerm S b N x) (originalWeightedC0_sum_norm_le S b N hs)

/-- Every full C0 test evaluates by the original weighted coefficient series. -/
theorem originalWeightedAtomicC0Dual_apply (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (g : C₀(ℝ, ℂ)) :
    originalWeightedAtomicC0Dual S b N hs g =
      ∑' x : S.subtype, originalWeightedC0Coefficient S b N x * g x := rfl

/-- The norm of the genuine original dual is bounded by its ORIGINAL variation at SAME N. -/
theorem originalWeightedAtomicC0Dual_norm_le (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) :
    ‖originalWeightedAtomicC0Dual S b N hs‖ ≤ ∑' x : S.subtype, weightedAtomicMassTerm S b N x :=
  LinearMap.mkContinuous_norm_le _ (tsum_nonneg (fun x => by unfold weightedAtomicMassTerm; positivity)) _

/-- Actual weighting cancels at EVERY original atom when the full weighted Schwartz test is used. -/
theorem originalWeightedC0Coefficient_schwartz_cancel (S : LocallyFiniteCarrier)
    (b : S.subtype → ℂ) (N : ℕ) (f : SchwartzMap ℝ ℂ) (x : S.subtype) :
    originalWeightedC0Coefficient S b N x * originalWeightedSchwartzC0 N f x = b x * f x := by
  have hwR : (1 + |(x : ℝ)|) ^ N ≠ 0 := by positivity
  have hw : (((1 + |(x : ℝ)|) ^ N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwR
  change (b x / (((1 + |(x : ℝ)|) ^ N : ℝ) : ℂ)) *
    ((((1 + |(x : ℝ)|) ^ N : ℝ) : ℂ) * f x) = b x * f x
  field_simp

/-- EVERY full Schwartz test recovers the genuine original atomic distribution. -/
theorem originalWeightedAtomicC0Dual_schwartz (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (f : SchwartzMap ℝ ℂ) :
    originalWeightedAtomicC0Dual S b N hs (originalWeightedSchwartzC0 N f) =
      weightedAtomicDistribution S b N hs f := by
  rw [originalWeightedAtomicC0Dual_apply, weightedAtomicDistribution_apply]
  exact tsum_congr (originalWeightedC0Coefficient_schwartz_cancel S b N f)

/-- The ACTUAL original weighted record of a strongly tempered distribution, with no extra data. -/
def originalStrongAtomicC0Dual (S : LocallyFiniteCarrier) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    StrongDual ℂ C₀(ℝ, ℂ) :=
  originalWeightedAtomicC0Dual S (fun x => T (S.isolationSchwartz x)) N hT.2

/-- Its genuine C0 norm is bounded by the SAME original isolation-coefficient variation. -/
theorem originalStrongAtomicC0Dual_norm_le (S : LocallyFiniteCarrier) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    ‖originalStrongAtomicC0Dual S N T hT‖ ≤ ∑' x : S.subtype, stronglyTemperedCoefficientTerm S N T x :=
  originalWeightedAtomicC0Dual_norm_le S _ N hT.2

/-- The complete original distribution is recovered on EVERY full Schwartz test internally. -/
theorem originalStrongAtomicC0Dual_schwartz (S : LocallyFiniteCarrier) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (f : SchwartzMap ℝ ℂ) :
    originalStrongAtomicC0Dual S N T hT (originalWeightedSchwartzC0 N f) = T f := by
  unfold originalStrongAtomicC0Dual
  calc
    _ = weightedAtomicDistribution S (fun x => T (S.isolationSchwartz x)) N hT.2 f :=
      originalWeightedAtomicC0Dual_schwartz S _ N hT.2 f
    _ = _ := congrArg (fun D : TemperedDistribution ℝ ℂ => D f)
      (stronglyTemperedAtomicAtExponent_eq_weightedAtomicDistribution S N T hT).symm

end
end MeyerGeneralProblem
