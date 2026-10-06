module

public import MeyerGeneralProblem.Distribution.WeightedAtomic
public import MeyerGeneralProblem.Distribution.DisjointAtomicIndependence

@[expose] public section

/-!
# Full Schwartz evaluation from the ORIGINAL strongly tempered record

The actual distribution equals its original isolation-coefficient sum on EVERY
Schwartz test. Local atomic uniqueness and compact-cutoff density pay the
identity. A bound on weighted test values therefore controls its actual action
by the ORIGINAL weighted absolute variation, without a replacement measure or
an assumed summation formula.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Whole local atomic distributions are equal when ALL original isolation actions agree. -/
theorem locallyAtomic_eq_of_isolationAction_eq (S : LocallyFiniteCarrier)
    (T U : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T)
    (hU : HasLocallyAtomicAction S U) (he : ∀ x : S.subtype,
      T (S.isolationSchwartz x) = U (S.isolationSchwartz x)) : T = U := by
  have hdiff : AtomicOnCarrier S (T - U) := by
    intro f hf
    change T f - U f = 0
    rw [hasLocallyAtomicAction_atomicOnCarrier S T hT f hf,
      hasLocallyAtomicAction_atomicOnCarrier S U hU f hf, sub_self]
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨x, hx⟩ := locallyAtomic_exists_isolationAction_ne_zero S (T - U)
    (atomicOnCarrier_hasLocallyAtomicAction S (T - U) hdiff) hne
  apply hx
  change T (S.isolationSchwartz x) - U (S.isolationSchwartz x) = 0
  rw [he x, sub_self]

/-- EVERY actual strongly tempered atomic distribution is its own original weighted sum. -/
theorem stronglyTemperedAtomicAtExponent_eq_weightedAtomicDistribution (S : LocallyFiniteCarrier)
    (N : ℕ) (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    T = weightedAtomicDistribution S (fun x => T (S.isolationSchwartz x)) N hT.2 :=
  locallyAtomic_eq_of_isolationAction_eq S T _ hT.1
    (weightedAtomicDistribution_mem_strongExponent S _ N hT.2).1
    (fun x => (weightedAtomicDistribution_isolation S _ N hT.2 x).symm)

/-- The original isolation-coefficient series evaluates EVERY Schwartz test exactly. -/
theorem stronglyTemperedAtomicAtExponent_apply_tsum (S : LocallyFiniteCarrier)
    (N : ℕ) (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (f : SchwartzMap ℝ ℂ) :
    T f = ∑' x : S.subtype, T (S.isolationSchwartz x) * f x := by
  calc
    T f = weightedAtomicDistribution S (fun x => T (S.isolationSchwartz x)) N hT.2 f :=
      congrArg (fun D : TemperedDistribution ℝ ℂ => D f)
        (stronglyTemperedAtomicAtExponent_eq_weightedAtomicDistribution S N T hT)
    _ = _ := rfl

/-- A whole-carrier weighted pointwise bound controls the GENUINE distributional action
by its ORIGINAL absolute coefficient variation at the SAME exponent. -/
theorem stronglyTemperedAtomicAtExponent_norm_apply_le (S : LocallyFiniteCarrier)
    (N : ℕ) (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (f : SchwartzMap ℝ ℂ) (K : ℝ)
    (hK : ∀ x : S.subtype, (1 + |(x : ℝ)|) ^ N * ‖f x‖ ≤ K) :
    ‖T f‖ ≤ K * ∑' x : S.subtype, stronglyTemperedCoefficientTerm S N T x := by
  have hs := weightedAtomic_samples_summable S (fun x => T (S.isolationSchwartz x)) N hT.2 f
  have hbound (x : S.subtype) :
      ‖T (S.isolationSchwartz x) * f x‖ ≤ K * stronglyTemperedCoefficientTerm S N T x := by
    have hw : 0 < (1 + |(x : ℝ)|) ^ N := by positivity
    have hf : ‖f x‖ ≤ K / (1 + |(x : ℝ)|) ^ N :=
      (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hK x)
    rw [norm_mul, stronglyTemperedCoefficientTerm]
    exact (mul_le_mul_of_nonneg_left hf (norm_nonneg _)).trans_eq (by ring)
  rw [stronglyTemperedAtomicAtExponent_apply_tsum S N T hT f]
  calc
    _ ≤ ∑' x : S.subtype, ‖T (S.isolationSchwartz x) * f x‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' x : S.subtype, K * stronglyTemperedCoefficientTerm S N T x :=
      hs.norm.tsum_le_tsum hbound (hT.2.mul_left K)
    _ = _ := tsum_mul_left

end

end MeyerGeneralProblem
