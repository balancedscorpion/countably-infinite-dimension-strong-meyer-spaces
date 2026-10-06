module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalArrayEmbedding
public import MeyerGeneralProblem.Distribution.StrongDilation
public import MeyerGeneralProblem.Distribution.LiteralAtomicSourceRecovery

@[expose] public section

/-! Whole original coefficient transport and exact Fourier normalization under
positive dilation. Neither a surrogate coefficient array nor an omitted
Jacobian is used in the actual constructed original records. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped FourierTransform

/-- Extending an atomic source to a larger carrier preserves EVERY original
coefficient, including points outside its actual support. -/
theorem extendedAtomicCoefficient_on_larger_carrier (S U : LocallyFiniteCarrier)
    (hSU : S.carrier ⊆ U.carrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T) (x : ℝ) :
    extendedAtomicCoefficient U T x = extendedAtomicCoefficient S T x := by
  classical
  by_cases hx : x ∈ U.carrier
  · rw [extendedAtomicCoefficient, dite_eq_left hx]
    exact atomic_isolation_apply_on_larger_carrier S U hSU T hT ⟨x, hx⟩
  · have hs : x ∉ S.carrier := fun h => hx (hSU h)
    simp only [extendedAtomicCoefficient, dite_eq_right hx, dite_eq_right hs]

/-- Actual pushforward preserves the original coefficient at EVERY scaled
point, retaining zero extension and the original isolation tests. -/
theorem extendedAtomicCoefficient_dilation (S : LocallyFiniteCarrier)
    (c : ℝ) (hc : 0 < c) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T) (x : ℝ) :
    extendedAtomicCoefficient (S.dilate c hc) (combDistributionDilation c hc.ne' T) (c * x) =
      extendedAtomicCoefficient S T x := by
  classical
  by_cases hx : x ∈ S.carrier
  · have hcx : c * x ∈ (S.dilate c hc).carrier := ⟨x, hx, rfl⟩
    rw [extendedAtomicCoefficient, dite_eq_left hcx, extendedAtomicCoefficient, dite_eq_left hx]
    exact combDistributionDilation_isolation_apply S c hc T
      (atomicOnCarrier_hasLocallyAtomicAction S T hT) ⟨x, hx⟩
  · have hcx : c * x ∉ (S.dilate c hc).carrier := by
      rintro ⟨y, hy, he⟩
      exact hx ((mul_left_cancel₀ hc.ne' he) ▸ hy)
    simp only [extendedAtomicCoefficient, dite_eq_right hx, dite_eq_right hcx]

/-- The genuine physical pushforward with its positive Fourier Jacobian
compensated. Its spectral coefficients then remain exactly the native ones. -/
def originalJacobianNormalizedDilation (c : ℝ) (hc : 0 < c)
    (T : TemperedDistribution ℝ ℂ) : TemperedDistribution ℝ ℂ :=
  (c : ℂ) • combDistributionDilation c hc.ne' T

/-- The inverse Jacobian cancels EXACTLY, as an identity of whole records. -/
theorem originalJacobianNormalizedDilation_fourier (c : ℝ) (hc : 0 < c)
    (T : TemperedDistribution ℝ ℂ) :
    𝓕 (originalJacobianNormalizedDilation c hc T) =
      combDistributionDilation c⁻¹ (inv_pos.mpr hc).ne' (𝓕 T) := by
  rw [originalJacobianNormalizedDilation, FourierTransform.fourier_smul,
    fourier_combDistributionDilation, smul_smul, abs_of_pos hc]
  have hscalar : (c : ℂ) * ((c⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne', Complex.ofReal_one]
  rw [hscalar, one_smul]

/-- BOTH original strong records of a normalized source retain their original
exponents; the physical scalar is included in the original weighted variation. -/
theorem originalJacobianNormalizedDilation_both_strong (A B : LocallyFiniteCarrier)
    (c : ℝ) (hc : 0 < c) (M N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent A M)
    (hFT : 𝓕 T ∈ stronglyTemperedAtomicAtExponent B N) :
    originalJacobianNormalizedDilation c hc T ∈ stronglyTemperedAtomicAtExponent (A.dilate c hc) M ∧
    𝓕 (originalJacobianNormalizedDilation c hc T) ∈
      stronglyTemperedAtomicAtExponent (B.dilate c⁻¹ (inv_pos.mpr hc)) N := by
  refine ⟨(stronglyTemperedAtomicAtExponent _ M).smul_mem (c : ℂ)
    (stronglyTemperedAtomicAtExponent_combDistributionDilation A c hc M T hT), ?_⟩
  rw [originalJacobianNormalizedDilation_fourier]
  exact stronglyTemperedAtomicAtExponent_combDistributionDilation B c⁻¹ (inv_pos.mpr hc) N (𝓕 T) hFT

end
end MeyerGeneralProblem
