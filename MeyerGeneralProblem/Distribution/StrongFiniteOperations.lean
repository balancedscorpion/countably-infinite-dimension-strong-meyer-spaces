module

public import MeyerGeneralProblem.Distribution.FiniteConvolutionCoefficients
public import MeyerGeneralProblem.Distribution.RestrictedAtomicRows

@[expose] public section

/-!
# Actual finite operations preserve ORIGINAL weighted absolute variation

Whole carrier translation, actual character multiplication and finite convolution
preserve original strong admission at the SAME exponent. The original isolation
coefficients are transported exactly; all coincident shifts and allowed zeros
remain included. No Fourier admissibility of a restriction is assumed.
-/
namespace MeyerGeneralProblem
noncomputable section
open scoped FourierTransform

/-- The actual point map on the WHOLE translated carrier. -/
def LocallyFiniteCarrier.translationPoint (S : LocallyFiniteCarrier) (a : ℝ)
    (x : S.subtype) : (S.translate a).subtype := ⟨a + (x : ℝ), ⟨x, x.property, rfl⟩⟩

theorem LocallyFiniteCarrier.translationPoint_bijective (S : LocallyFiniteCarrier) (a : ℝ) :
    Function.Bijective (S.translationPoint a) := by
  constructor
  · intro x y he
    exact Subtype.ext (add_left_cancel (congrArg Subtype.val he))
  · rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Exact bijection of all original allowed points, independently of their coefficients. -/
def LocallyFiniteCarrier.translationEquiv (S : LocallyFiniteCarrier) (a : ℝ) :
    S.subtype ≃ (S.translate a).subtype :=
  Equiv.ofBijective (S.translationPoint a) (S.translationPoint_bijective a)

theorem LocallyFiniteCarrier.translationEquiv_val (S : LocallyFiniteCarrier) (a : ℝ)
    (x : S.subtype) : (S.translationEquiv a x : ℝ) = a + (x : ℝ) := rfl

/-- Inverse translation returns the entire original carrier. -/
theorem LocallyFiniteCarrier.translate_neg_eq_self (S : LocallyFiniteCarrier) (a : ℝ) :
    (S.translate a).translate (-a) = S := by
  apply LocallyFiniteCarrier.ext
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    simpa only [neg_add_cancel_left] using hx
  · intro hy
    exact ⟨a + y, ⟨y, hy, rfl⟩, by ring⟩

/-- Actual inverse pushforward translation returns the original distribution. -/
theorem combDistributionTranslation_neg_apply (a : ℝ) (T : TemperedDistribution ℝ ℂ) :
    combDistributionTranslation (-a) (combDistributionTranslation a T) = T := by
  ext f
  rw [combDistributionTranslation_apply, combDistributionTranslation_apply]
  congr 1
  ext x
  rw [combSchwartzTranslation_apply, combSchwartzTranslation_apply]
  congr 1
  ring

/-- Every original isolation action survives actual translation exactly. -/
theorem combDistributionTranslation_isolation_apply (S : LocallyFiniteCarrier) (a : ℝ)
    (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T) (x : S.subtype) :
    combDistributionTranslation a T ((S.translate a).isolationSchwartz (S.translationEquiv a x)) =
      T (S.isolationSchwartz x) := by
  have hz : SchwartzVanishesOn S
      (combSchwartzTranslation a ((S.translate a).isolationSchwartz (S.translationEquiv a x)) -
        S.isolationSchwartz x) := by
    intro y hy
    let yS : S.subtype := ⟨y, hy⟩
    rw [sub_apply, combSchwartzTranslation_apply]
    apply sub_eq_zero.mpr
    change (S.translate a).isolationSchwartz (S.translationEquiv a x)
      (S.translationEquiv a yS) = S.isolationSchwartz x yS
    simp only [LocallyFiniteCarrier.isolationSchwartz_apply_subtype,
      (S.translationEquiv a).injective.eq_iff]
  have he := (hasLocallyAtomicAction_atomicOnCarrier S T hT) _ hz
  rw [map_sub, sub_eq_zero] at he
  exact he

/-- Actual translations change polynomial weights by a finite constant. -/
theorem originalTranslationWeight_le (a x : ℝ) :
    1 + |x| ≤ (1 + |a|) * (1 + |a + x|) := by
  have h := abs_sub (a + x) a
  rw [add_sub_cancel_left] at h
  nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg (a + x))]

/-- Whole-carrier original coefficient bound at the SAME exponent. -/
theorem stronglyTemperedCoefficientTerm_translation_le (S : LocallyFiniteCarrier)
    (a : ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T)
    (x : S.subtype) :
    stronglyTemperedCoefficientTerm (S.translate a) N (combDistributionTranslation a T)
      (S.translationEquiv a x) ≤ (1 + |a|) ^ N * stronglyTemperedCoefficientTerm S N T x := by
  unfold stronglyTemperedCoefficientTerm
  rw [combDistributionTranslation_isolation_apply S a T hT x, S.translationEquiv_val]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |(x : ℝ)|)
    (originalTranslationWeight_le a x) N
  rw [mul_pow] at hp
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_left hp (norm_nonneg (T (S.isolationSchwartz x)))
  nlinarith

/-- Translation preserves the GENUINE original weighted absolute mass at the SAME exponent. -/
theorem stronglyTemperedAtomicAtExponent_combDistributionTranslation (S : LocallyFiniteCarrier)
    (a : ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    combDistributionTranslation a T ∈ stronglyTemperedAtomicAtExponent (S.translate a) N := by
  refine ⟨atomicOnCarrier_hasLocallyAtomicAction _ _
    (atomicOnCarrier_combDistributionTranslation S T
      (hasLocallyAtomicAction_atomicOnCarrier S T hT.1) a), ?_⟩
  rw [← (S.translationEquiv a).summable_iff]
  apply Summable.of_nonneg_of_le (fun x => by unfold stronglyTemperedCoefficientTerm; positivity)
    (stronglyTemperedCoefficientTerm_translation_le S a N T hT.1)
    (hT.2.mul_left ((1 + |a|) ^ N))

/-- Exact membership equivalence on the COMPLETE fixed-exponent original spaces. -/
theorem stronglyTemperedAtomicAtExponent_translation_iff (S : LocallyFiniteCarrier)
    (a : ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ) :
    combDistributionTranslation a T ∈ stronglyTemperedAtomicAtExponent (S.translate a) N ↔
      T ∈ stronglyTemperedAtomicAtExponent S N := by
  constructor
  · intro h
    have hi := stronglyTemperedAtomicAtExponent_combDistributionTranslation (S.translate a)
      (-a) N _ h
    simpa only [S.translate_neg_eq_self a, combDistributionTranslation_neg_apply] using hi
  · exact stronglyTemperedAtomicAtExponent_combDistributionTranslation S a N T

/-- Whole original coefficient masses are unchanged by actual unit-character multiplication. -/
theorem stronglyTemperedCoefficientTerm_modulation_eq (S : LocallyFiniteCarrier)
    (a : ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T)
    (x : S.subtype) : stronglyTemperedCoefficientTerm S N (combDistributionModulation a T) x =
      stronglyTemperedCoefficientTerm S N T x := by
  simp only [stronglyTemperedCoefficientTerm,
    combDistributionModulation_isolation_apply S T hT, norm_mul,
    norm_combModulationCharacter, one_mul]

/-- The ORIGINAL same-exponent strong record survives genuine character multiplication. -/
theorem stronglyTemperedAtomicAtExponent_combDistributionModulation (S : LocallyFiniteCarrier)
    (a : ℝ) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    combDistributionModulation a T ∈ stronglyTemperedAtomicAtExponent S N := by
  refine ⟨atomicOnCarrier_hasLocallyAtomicAction _ _
    (atomicOnCarrier_combDistributionModulation S T
      (hasLocallyAtomicAction_atomicOnCarrier S T hT.1) a), ?_⟩
  have he : stronglyTemperedCoefficientTerm S N (combDistributionModulation a T) =
      stronglyTemperedCoefficientTerm S N T := funext
    (stronglyTemperedCoefficientTerm_modulation_eq S a N T hT.1)
  rw [he]
  exact hT.2

/-- Finite convolution preserves actual original strong mass, with ALL shift collisions retained. -/
theorem stronglyTemperedAtomicAtExponent_finiteCombConvolution {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (a : ι → ℝ) (c : ι → ℂ) :
    finiteCombConvolution a c T ∈
      stronglyTemperedAtomicAtExponent (finiteCombConvolutionCarrier S a) N := by
  rw [finiteCombConvolution_apply]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply stronglyTemperedAtomicAtExponent_mono_carrier
    (show (S.translate (a i)).carrier ⊆ (finiteCombConvolutionCarrier S a).carrier by
      intro x hx; exact Set.mem_iUnion.mpr ⟨i, hx⟩)
  exact stronglyTemperedAtomicAtExponent_combDistributionTranslation S (a i) N T hT

/-- A finite genuine exponential multiplier preserves the original SAME-exponent record. -/
theorem stronglyTemperedAtomicAtExponent_finiteExponentialMultiplication {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (a : ι → ℝ) (c : ι → ℂ) :
    finiteExponentialMultiplication a c T ∈ stronglyTemperedAtomicAtExponent S N := by
  simp only [finiteExponentialMultiplication, _root_.sum_apply, smul_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (stronglyTemperedAtomicAtExponent_combDistributionModulation S (a i) N T hT)

/-- BOTH original records survive a genuine finite exponential multiplier on their whole carriers. -/
theorem stronglyTemperedOriginalPair_finiteExponentialMultiplication {ι : Type*} [Fintype ι]
    (S U : LocallyFiniteCarrier) (M N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent U N) (a : ι → ℝ) (c : ι → ℂ) :
    finiteExponentialMultiplication a c T ∈ stronglyTemperedAtomicAtExponent S M ∧
    𝓕 (finiteExponentialMultiplication a c T) ∈
      stronglyTemperedAtomicAtExponent (finiteCombConvolutionCarrier U a) N := by
  refine ⟨stronglyTemperedAtomicAtExponent_finiteExponentialMultiplication S M T hT a c, ?_⟩
  rw [fourier_finiteExponentialMultiplication]
  exact stronglyTemperedAtomicAtExponent_finiteCombConvolution U N (𝓕 T) hF a c

/-- BOTH original records survive genuine finite convolution, at their SAME exponents. -/
theorem stronglyTemperedOriginalPair_finiteCombConvolution {ι : Type*} [Fintype ι]
    (S U : LocallyFiniteCarrier) (M N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent U N) (a : ι → ℝ) (c : ι → ℂ) :
    finiteCombConvolution a c T ∈
      stronglyTemperedAtomicAtExponent (finiteCombConvolutionCarrier S a) M ∧
    𝓕 (finiteCombConvolution a c T) ∈ stronglyTemperedAtomicAtExponent U N := by
  refine ⟨stronglyTemperedAtomicAtExponent_finiteCombConvolution S M T hT a c, ?_⟩
  rw [fourier_finiteCombConvolution]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (stronglyTemperedAtomicAtExponent_combDistributionModulation U (-a i) N (𝓕 T) hF)

end
end MeyerGeneralProblem
