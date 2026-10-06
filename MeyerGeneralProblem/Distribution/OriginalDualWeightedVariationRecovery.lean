module

public import MeyerGeneralProblem.Distribution.OriginalDualIsolationVariation

@[expose] public section

/-! Recover BOTH ORIGINAL same-N weighted coefficient variations internally
from the actual product-C0 dual norm and its full carrier constraints. General
constrained duals yield WHOLE original strong records; no atomicity, summability
or norm/variation certificate is supplied. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty FourierTransform

/-- The actual weighted isolator and its correctly scaled ordinary C0 isolator
agree at EVERY carrier point; the full difference belongs to its vanishing ideal. -/
theorem originalWeightedIsolationC0_difference_vanishes (S : LocallyFiniteCarrier) (N : ℕ) (x : S.subtype) :
    ∀ y : S.subtype,
      (originalWeightedSchwartzC0 N (S.isolationSchwartz x) -
        (((1 + |(x : ℝ)|) ^ N : ℝ) : ℂ) • originalIsolationC0 S x) y = 0 := by
  intro y
  change ((((1 + |(y : ℝ)|) ^ N : ℝ) : ℂ) * S.isolationSchwartz x y) -
    (((1 + |(x : ℝ)|) ^ N : ℝ) : ℂ) * S.isolationSchwartz x y = 0
  by_cases hy : y = x
  · subst y
    ring
  · rw [S.isolationSchwartz_apply_subtype]
    simp [hy]

/-- The WHOLE physical distribution's original coefficient is recovered from
its genuine C0 record with the literal SAME-N atom weight. -/
theorem originalWeightedDual_physical_isolation (S : LocallyFiniteCarrier) (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (hq : q ∈ originalWeightedDualCarrierConstraints S)
    (x : S.subtype) :
    originalWeightedDualPhysicalDistribution N q (S.isolationSchwartz x) =
      (((1 + |(x : ℝ)|) ^ N : ℝ) : ℂ) * q (originalIsolationC0 S x, 0) := by
  have h := (hq _ (originalWeightedIsolationC0_difference_vanishes S N x)).1
  change originalDualPhysicalC0Record q (originalWeightedSchwartzC0 N (S.isolationSchwartz x) -
    (((1 + |(x : ℝ)|) ^ N : ℝ) : ℂ) • originalIsolationC0 S x) = 0 at h
  rw [map_sub, map_smul] at h
  exact sub_eq_zero.mp h

/-- The WHOLE spectral distribution's original coefficient is recovered at the SAME original atom weight. -/
theorem originalWeightedDual_spectral_isolation (S : LocallyFiniteCarrier) (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (hq : q ∈ originalWeightedDualCarrierConstraints S)
    (x : S.subtype) :
    originalWeightedDualSpectralDistribution N q (S.isolationSchwartz x) =
      (((1 + |(x : ℝ)|) ^ N : ℝ) : ℂ) * q (0, originalIsolationC0 S x) := by
  have h := (hq _ (originalWeightedIsolationC0_difference_vanishes S N x)).2
  change originalDualSpectralC0Record q (originalWeightedSchwartzC0 N (S.isolationSchwartz x) -
    (((1 + |(x : ℝ)|) ^ N : ℝ) : ℂ) • originalIsolationC0 S x) = 0 at h
  rw [map_sub, map_smul] at h
  exact sub_eq_zero.mp h

/-- The original physical weighted mass is EXACTLY the genuine dual isolation mass. -/
theorem originalWeightedDual_physical_mass (S : LocallyFiniteCarrier) (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (hq : q ∈ originalWeightedDualCarrierConstraints S)
    (x : S.subtype) :
    stronglyTemperedCoefficientTerm S N (originalWeightedDualPhysicalDistribution N q) x =
      ‖q (originalIsolationC0 S x, 0)‖ := by
  unfold stronglyTemperedCoefficientTerm
  rw [originalWeightedDual_physical_isolation S N q hq x, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + |(x : ℝ)|) ^ N)]
  have hn : (1 + |(x : ℝ)|) ^ N ≠ 0 := by positivity
  field_simp

/-- The original spectral weighted mass is EXACTLY its genuine dual isolation mass at SAME N. -/
theorem originalWeightedDual_spectral_mass (S : LocallyFiniteCarrier) (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (hq : q ∈ originalWeightedDualCarrierConstraints S)
    (x : S.subtype) :
    stronglyTemperedCoefficientTerm S N (originalWeightedDualSpectralDistribution N q) x =
      ‖q (0, originalIsolationC0 S x)‖ := by
  unfold stronglyTemperedCoefficientTerm
  rw [originalWeightedDual_spectral_isolation S N q hq x, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + |(x : ℝ)|) ^ N)]
  have hn : (1 + |(x : ℝ)|) ^ N ≠ 0 := by positivity
  field_simp

/-- The COMPLETE original physical weighted coefficient variation is summable internally. -/
theorem originalWeightedDual_physical_original_summable (S : LocallyFiniteCarrier) (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (hq : q ∈ originalWeightedDualCarrierConstraints S) :
    Summable (stronglyTemperedCoefficientTerm S N (originalWeightedDualPhysicalDistribution N q)) := by
  convert originalDualIsolation_physical_summable S q using 1
  funext x
  exact originalWeightedDual_physical_mass S N q hq x

/-- The COMPLETE original spectral weighted variation is summable at the SAME N internally. -/
theorem originalWeightedDual_spectral_original_summable (S : LocallyFiniteCarrier) (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (hq : q ∈ originalWeightedDualCarrierConstraints S) :
    Summable (stronglyTemperedCoefficientTerm S N (originalWeightedDualSpectralDistribution N q)) := by
  convert originalDualIsolation_spectral_summable S q using 1
  funext x
  exact originalWeightedDual_spectral_mass S N q hq x

/-- EVERY carrier-constrained dual gives BOTH WHOLE ORIGINAL strong records at SAME N,
with local atomicity AND original weighted summability derived internally. -/
theorem originalWeightedDual_carrier_both_original_strong (S : LocallyFiniteCarrier) (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (hq : q ∈ originalWeightedDualCarrierConstraints S) :
    originalWeightedDualPhysicalDistribution N q ∈ stronglyTemperedAtomicAtExponent S N ∧
      originalWeightedDualSpectralDistribution N q ∈ stronglyTemperedAtomicAtExponent S N := by
  have ha := originalWeightedDualCarrierConstraints_atomic S N q hq
  exact ⟨⟨atomicOnCarrier_hasLocallyAtomicAction S _ ha.1,
    originalWeightedDual_physical_original_summable S N q hq⟩,
    ⟨atomicOnCarrier_hasLocallyAtomicAction S _ ha.2,
      originalWeightedDual_spectral_original_summable S N q hq⟩⟩

/-- The ACTUAL pair dual norm bounds the SUM of BOTH COMPLETE ORIGINAL SAME-N variations. -/
theorem originalWeightedDual_carrier_original_variation_le_norm (S : LocallyFiniteCarrier) (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (hq : q ∈ originalWeightedDualCarrierConstraints S) :
    (∑' x : S.subtype, stronglyTemperedCoefficientTerm S N (originalWeightedDualPhysicalDistribution N q) x) +
      (∑' x : S.subtype, stronglyTemperedCoefficientTerm S N (originalWeightedDualSpectralDistribution N q) x) ≤
        ‖WeakDual.toStrongDual q‖ := by
  simpa only [originalWeightedDual_physical_mass S N q hq, originalWeightedDual_spectral_mass S N q hq] using
    originalDualIsolation_pair_mass_le_norm S q

/-- EVERY genuine compact Fourier carrier-ball member yields BOTH WHOLE ORIGINAL
strong records at SAME N and original TV-sum at most one; membership ALONE suffices. -/
theorem originalWeightedDualSupportedFourierPairBall_original_strong (S : LocallyFiniteCarrier) (N : ℕ)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (hq : q ∈ originalWeightedDualSupportedFourierPairBall S N) :
    originalWeightedDualPhysicalDistribution N q ∈ stronglyTemperedAtomicAtExponent S N ∧
      𝓕 (originalWeightedDualPhysicalDistribution N q) ∈ stronglyTemperedAtomicAtExponent S N ∧
      originalStrongPairVariation S N (originalWeightedDualPhysicalDistribution N q) ≤ 1 := by
  have ha := originalWeightedDual_carrier_both_original_strong S N q hq.2
  have hv := originalWeightedDual_carrier_original_variation_le_norm S N q hq.2
  have hb : ‖WeakDual.toStrongDual q‖ ≤ 1 := by
    have hball := hq.1.1
    change WeakDual.toStrongDual q ∈ Metric.closedBall 0 1 at hball
    have hd := Metric.mem_closedBall.mp hball
    exact (dist_zero_right (WeakDual.toStrongDual q)).symm.le.trans hd
  refine ⟨ha.1, hq.1.2 ▸ ha.2, ?_⟩
  unfold originalStrongPairVariation
  rw [← hq.1.2]
  exact hv.trans hb

/-- The genuine compact carrier ball realizes EXACTLY the original SAME-N TV-sum
unit Fourier pairs. BOTH directions are internal; no recovery certificate is assumed. -/
theorem originalStrong_unit_pair_iff_supported_dual (S : LocallyFiniteCarrier) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) :
    (T ∈ stronglyTemperedAtomicAtExponent S N ∧ 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N ∧
      originalStrongPairVariation S N T ≤ 1) ↔
    ∃ q ∈ originalWeightedDualSupportedFourierPairBall S N, originalWeightedDualPhysicalDistribution N q = T := by
  constructor
  · rintro ⟨hT, hF, hu⟩
    obtain ⟨q, hq, hp, hs⟩ := originalStrongPair_exists_weighted_dual_supported_ball S N T hT hF hu
    exact ⟨q, hq, hp⟩
  · rintro ⟨q, hq, hp⟩
    simpa only [hp] using originalWeightedDualSupportedFourierPairBall_original_strong S N q hq

/-- The internally constructed original pair dual has norm EXACTLY the SUM of
BOTH original SAME-N weighted absolute variations. -/
theorem originalStrongPairC0Dual_norm_eq_variation (S : LocallyFiniteCarrier) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent S N) :
    ‖originalStrongPairC0Dual S N T hT hF‖ = originalStrongPairVariation S N T := by
  apply le_antisymm (originalStrongPairC0Dual_norm_le S N T hT hF)
  have h := originalWeightedDual_carrier_original_variation_le_norm S N
    (originalStrongPairC0Dual S N T hT hF).toWeakDual
    (originalStrongPairC0Dual_carrierConstraints S N T hT hF)
  simpa only [originalStrongPairC0Dual_physical, originalStrongPairC0Dual_spectral,
    StrongDual.toStrongDual_toWeakDual, originalStrongPairVariation] using h

end
end MeyerGeneralProblem
