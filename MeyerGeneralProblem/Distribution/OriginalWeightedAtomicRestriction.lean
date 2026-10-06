module

public import MeyerGeneralProblem.Distribution.OriginalStrongEvaluation
public import MeyerGeneralProblem.Distribution.RestrictedAtomicRows
public import MeyerGeneralProblem.Distribution.FiniteConvolutionCoefficients

@[expose] public section

/-! Actual weighted atomic restrictions of ONE original record.
Every constructor is a genuine continuous Schwartz functional and retains the
original isolation coefficients at the SAME exponent. No Fourier-pair hypothesis
or conclusion is made for a restriction. Pair recovery is proved separately. -/
namespace MeyerGeneralProblem
noncomputable section

/-- Original isolation coefficients, retained exactly on the chosen actual set. -/
def originalAtomicRestrictionCoefficient (S : LocallyFiniteCarrier) (A : Set ℝ)
    (T : TemperedDistribution ℝ ℂ) (x : S.subtype) : ℂ := by
  classical
  exact if (x : ℝ) ∈ A then T (S.isolationSchwartz x) else 0

/-- Literal restriction decreases each ORIGINAL weighted coefficient term. -/
theorem originalAtomicRestrictionCoefficient_weight_le (S : LocallyFiniteCarrier)
    (A : Set ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ) (x : S.subtype) :
    weightedAtomicMassTerm S (originalAtomicRestrictionCoefficient S A T) N x ≤
      stronglyTemperedCoefficientTerm S N T x := by
  classical
  by_cases hx : (x : ℝ) ∈ A
  · simp [weightedAtomicMassTerm, originalAtomicRestrictionCoefficient, hx,
      stronglyTemperedCoefficientTerm]
  · simp [weightedAtomicMassTerm, originalAtomicRestrictionCoefficient, hx,
      stronglyTemperedCoefficientTerm]
    exact div_nonneg (norm_nonneg _) (by positivity)

/-- The actual original restriction has finite weighted variation at the SAME exponent. -/
theorem originalAtomicRestrictionCoefficient_weight_summable (S : LocallyFiniteCarrier)
    (A : Set ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    Summable (weightedAtomicMassTerm S (originalAtomicRestrictionCoefficient S A T) N) :=
  Summable.of_nonneg_of_le (fun x => by unfold weightedAtomicMassTerm; positivity)
    (originalAtomicRestrictionCoefficient_weight_le S A N T) hT.2

/-- The genuine tempered distribution defined by the restricted ORIGINAL atomic record. -/
def originalWeightedAtomicRestriction (S : LocallyFiniteCarrier) (A : Set ℝ)
    (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) : TemperedDistribution ℝ ℂ :=
  weightedAtomicDistribution S (originalAtomicRestrictionCoefficient S A T) N
    (originalAtomicRestrictionCoefficient_weight_summable S A N T hT)

/-- Its actual canonical isolation action is exactly the original coefficient or zero. -/
theorem originalWeightedAtomicRestriction_isolation (S : LocallyFiniteCarrier) (A : Set ℝ)
    (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (x : S.subtype) :
    originalWeightedAtomicRestriction S A N T hT (S.isolationSchwartz x) =
      originalAtomicRestrictionCoefficient S A T x := weightedAtomicDistribution_isolation _ _ _ _ x

/-- This ONE actual record is strongly tempered at the SAME exponent on the original carrier. -/
theorem originalWeightedAtomicRestriction_mem_strongExponent (S : LocallyFiniteCarrier)
    (A : Set ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    originalWeightedAtomicRestriction S A N T hT ∈ stronglyTemperedAtomicAtExponent S N :=
  weightedAtomicDistribution_mem_strongExponent _ _ _ _

/-- Zero extension is the literal original coefficient restricted at EVERY real point. -/
theorem originalWeightedAtomicRestriction_extendedCoefficient (S : LocallyFiniteCarrier)
    (A : Set ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (x : ℝ) :
    extendedAtomicCoefficient S (originalWeightedAtomicRestriction S A N T hT) x =
      (by classical exact if x ∈ A then extendedAtomicCoefficient S T x else 0) := by
  classical
  by_cases hx : x ∈ S.carrier
  · simp only [extendedAtomicCoefficient, dite_eq_left hx]
    rw [originalWeightedAtomicRestriction_isolation]
    simp only [originalAtomicRestrictionCoefficient]
  · simp [extendedAtomicCoefficient, hx]

/-- Actual atomicity on the restricted set follows from the original zero rows. -/
theorem originalWeightedAtomicRestriction_atomicOnCarrier (S : LocallyFiniteCarrier)
    (A : Set ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    AtomicOnCarrier (S.restrict (S.carrier ∩ A) Set.inter_subset_left)
      (originalWeightedAtomicRestriction S A N T hT) := by
  apply (atomicOnCarrier_restrict_iff S _ Set.inter_subset_left _).mpr
  refine ⟨hasLocallyAtomicAction_atomicOnCarrier S _
    (originalWeightedAtomicRestriction_mem_strongExponent S A N T hT).1, ?_⟩
  intro x hx
  have hA : (x : ℝ) ∉ A := fun h => hx ⟨x.property, h⟩
  rw [originalWeightedAtomicRestriction_isolation]
  simp [originalAtomicRestrictionCoefficient, hA]

/-- Subtraction produces the complementary ORIGINAL record, before any Fourier assertion. -/
theorem originalWeightedAtomicRestriction_complement_atomicOnCarrier (S : LocallyFiniteCarrier)
    (A : Set ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    AtomicOnCarrier (S.restrict (S.carrier \ A) Set.sdiff_subset)
      (T - originalWeightedAtomicRestriction S A N T hT) := by
  apply (atomicOnCarrier_restrict_iff S _ Set.sdiff_subset _).mpr
  refine ⟨hasLocallyAtomicAction_atomicOnCarrier S _
    ((stronglyTemperedAtomicAtExponent S N).sub_mem hT
      (originalWeightedAtomicRestriction_mem_strongExponent S A N T hT)).1, ?_⟩
  intro x hx
  have hA : (x : ℝ) ∈ A := by
    by_contra hn
    exact hx ⟨x.property, hn⟩
  change T (S.isolationSchwartz x) - originalWeightedAtomicRestriction S A N T hT (S.isolationSchwartz x) = 0
  rw [originalWeightedAtomicRestriction_isolation]
  simp [originalAtomicRestrictionCoefficient, hA]

/-- Literal restriction and its complement partition EVERY ORIGINAL weighted
term exactly at the SAME exponent; no triangle-inequality loss is introduced. -/
theorem originalWeightedAtomicRestriction_weight_partition (S : LocallyFiniteCarrier)
    (A : Set ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (x : S.subtype) :
    stronglyTemperedCoefficientTerm S N (originalWeightedAtomicRestriction S A N T hT) x +
      stronglyTemperedCoefficientTerm S N (T - originalWeightedAtomicRestriction S A N T hT) x =
        stronglyTemperedCoefficientTerm S N T x := by
  classical
  unfold stronglyTemperedCoefficientTerm
  change ‖originalWeightedAtomicRestriction S A N T hT (S.isolationSchwartz x)‖ / _ +
    ‖T (S.isolationSchwartz x) - originalWeightedAtomicRestriction S A N T hT (S.isolationSchwartz x)‖ / _ = _
  rw [originalWeightedAtomicRestriction_isolation]
  by_cases hx : (x : ℝ) ∈ A <;> simp [originalAtomicRestrictionCoefficient, hx]

end
end MeyerGeneralProblem
