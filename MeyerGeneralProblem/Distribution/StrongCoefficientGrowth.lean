module

public import MeyerGeneralProblem.Distribution.MeyerSpace

@[expose] public section

/-!
# Polynomial finite-set growth from the exact strong coefficient condition

The strong condition uses the actual isolation-Schwartz values. It bounds
their variation on every finite set inside a ball. This provides a direct
test against a future crystalline witness without presupposing a measure
total-variation API or the existence of that witness.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- All actual carrier points in the closed radius-R ball, enumerated
using the carrier's proved local finiteness. -/
def carrierFiniteBall (S : LocallyFiniteCarrier) (R : ℝ) : Finset S.subtype :=
  ((S.finite_inter_Icc (-R) R).preimage
    (Set.injOn_of_injective Subtype.val_injective)).toFinset

/-- The finite ball contains exactly the actual carrier points of
absolute value at most R, with no selected subsequence or multiplicities. -/
theorem mem_carrierFiniteBall_iff (S : LocallyFiniteCarrier) (R : ℝ) (x : S.subtype) :
    x ∈ carrierFiniteBall S R ↔ |(x:ℝ)| ≤ R := by
  simp only [carrierFiniteBall, Set.Finite.mem_toFinset, Set.mem_preimage,
    Set.mem_inter_iff, Set.mem_Icc, abs_le]
  exact and_iff_right (show (x:ℝ) ∈ S.carrier from x.property)

/-- Every term of the exact strong coefficient series is nonnegative. -/
theorem stronglyTemperedCoefficientTerm_nonneg (S : LocallyFiniteCarrier)
    (N : ℕ) (T : TemperedDistribution ℝ ℂ) (x : S.subtype) :
    0 ≤ stronglyTemperedCoefficientTerm S N T x := by
  unfold stronglyTemperedCoefficientTerm
  positivity

/-- Actual isolation coefficients inside radius R have polynomial
finite-set variation whenever the exact strong series is summable. -/
theorem finiteSetVariation_le_of_strongCoefficientSummable
    (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hs : Summable (stronglyTemperedCoefficientTerm S N T))
    (F : Finset S.subtype) {R : ℝ} (hR : 0 ≤ R)
    (hF : ∀ x ∈ F, |(x : ℝ)| ≤ R) :
    (∑ x ∈ F, ‖T (S.isolationSchwartz x)‖) ≤
      (1+R)^N * ∑' x : S.subtype, stronglyTemperedCoefficientTerm S N T x := by
  have hp (x : S.subtype) : 0 < (1+|(x:ℝ)|)^N := by positivity
  calc
    _ ≤ ∑ x ∈ F, (1+R)^N * stronglyTemperedCoefficientTerm S N T x := by
      apply Finset.sum_le_sum
      intro x hx
      have he : ‖T (S.isolationSchwartz x)‖ =
          (1+|(x:ℝ)|)^N * stronglyTemperedCoefficientTerm S N T x := by
        unfold stronglyTemperedCoefficientTerm
        field_simp
      rw [he]
      apply mul_le_mul_of_nonneg_right _ (stronglyTemperedCoefficientTerm_nonneg S N T x)
      exact pow_le_pow_left₀ (by positivity) (by linarith [hF x hx]) N
    _ = (1+R)^N * ∑ x ∈ F, stronglyTemperedCoefficientTerm S N T x := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum F (fun x _ => stronglyTemperedCoefficientTerm_nonneg S N T x))
      (by positivity)

/-- The exact strong coefficient condition gives polynomial variation
on the entire genuine finite carrier ball. -/
theorem finiteBallVariation_le_of_strongCoefficientSummable
    (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hs : Summable (stronglyTemperedCoefficientTerm S N T)) {R : ℝ} (hR : 0 ≤ R) :
    (∑ x ∈ carrierFiniteBall S R, ‖T (S.isolationSchwartz x)‖) ≤
      (1+R)^N * ∑' x : S.subtype, stronglyTemperedCoefficientTerm S N T x :=
  finiteSetVariation_le_of_strongCoefficientSummable S N T hs (carrierFiniteBall S R) hR
    (fun x hx => (mem_carrierFiniteBall_iff S R x).mp hx)

/-- The finite-ball estimate uses the coefficients of any actual local
atomic presentation, by proved uniqueness of isolation coefficients. -/
theorem finiteBallCoefficientVariation_le_of_strongCoefficientSummable
    (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (a : S.subtype → ℂ) (ha : IsLocallyAtomicCoefficientFamily S T a)
    (hs : Summable (stronglyTemperedCoefficientTerm S N T)) {R : ℝ} (hR : 0 ≤ R) :
    (∑ x ∈ carrierFiniteBall S R, ‖a x‖) ≤
      (1+R)^N * ∑' x : S.subtype, stronglyTemperedCoefficientTerm S N T x := by
  simp_rw [locallyAtomicCoefficient_eq_isolationAction S T a ha]
  exact finiteBallVariation_le_of_strongCoefficientSummable S N T hs hR

/-- A superpolynomial finite-set variation test excludes every exponent
of the exact strong coefficient series. No simultaneous atomicity is inferred. -/
theorem not_summable_strongCoefficient_of_superpolynomial_variation
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hgrowth : ∀ (N : ℕ) (C : ℝ), ∃ R ≥ 0, ∃ F : Finset S.subtype,
      (∀ x ∈ F, |(x:ℝ)| ≤ R) ∧ C*(1+R)^N < ∑ x ∈ F, ‖T (S.isolationSchwartz x)‖)
    (N : ℕ) : ¬ Summable (stronglyTemperedCoefficientTerm S N T) := by
  intro hs
  obtain ⟨R,hR,F,hF,hbig⟩ := hgrowth N (∑' x : S.subtype, stronglyTemperedCoefficientTerm S N T x)
  have hbound := finiteSetVariation_le_of_strongCoefficientSummable S N T hs F hR hF
  nlinarith

/-- The variation test rules out membership in the actual strong atomic
subspace, not merely a newly defined growth proxy. -/
theorem not_mem_stronglyTemperedAtomicOnCarrier_of_superpolynomial_variation
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hgrowth : ∀ (N : ℕ) (C : ℝ), ∃ R ≥ 0, ∃ F : Finset S.subtype,
      (∀ x ∈ F, |(x:ℝ)| ≤ R) ∧ C*(1+R)^N < ∑ x ∈ F, ‖T (S.isolationSchwartz x)‖) :
    T ∉ StronglyTemperedAtomicOnCarrier S := by
  intro h
  obtain ⟨N,_,hs⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff S T).mp h
  exact not_summable_strongCoefficient_of_superpolynomial_variation S T hgrowth N hs

/-- Physical-side superpolynomial variation excludes membership in the
actual two-sided strong Meyer subspace. Atomicity remains a separate obligation. -/
theorem not_mem_stronglyTemperedMeyerSpace_of_superpolynomial_variation
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hgrowth : ∀ (N : ℕ) (C : ℝ), ∃ R ≥ 0, ∃ F : Finset S.subtype,
      (∀ x ∈ F, |(x:ℝ)| ≤ R) ∧ C*(1+R)^N < ∑ x ∈ F, ‖T (S.isolationSchwartz x)‖) :
    T ∉ StronglyTemperedMeyerSpace S := by
  intro h
  exact not_mem_stronglyTemperedAtomicOnCarrier_of_superpolynomial_variation S T hgrowth h.1

end

end MeyerGeneralProblem
