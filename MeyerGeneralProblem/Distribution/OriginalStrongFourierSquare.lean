module

public import MeyerGeneralProblem.Distribution.StrongFiniteOperations
public import MeyerGeneralProblem.Distribution.CombScaling

@[expose] public section

/-! The actual double Fourier transform is physical reflection. ALL original
isolation coefficients and SAME-exponent absolute weights are transported on
the whole reflected carrier. No reflection or Fourier-growth certificate is assumed. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped FourierTransform

/-- Actual whole reflected carrier, with literal local finiteness. -/
def LocallyFiniteCarrier.reflect (S : LocallyFiniteCarrier) : LocallyFiniteCarrier where
  carrier := (fun x : ℝ => -x) '' S.carrier
  finite_inter_Icc a b := by
    apply ((S.finite_inter_Icc (-b) (-a)).image (fun x : ℝ => -x)).subset
    rintro y ⟨⟨x, hx, rfl⟩, hlo, hhi⟩
    exact ⟨x, ⟨hx, by linarith, by linarith⟩, rfl⟩

/-- The whole geometric reflection is an actual bijection. -/
def LocallyFiniteCarrier.reflectionEquiv (S : LocallyFiniteCarrier) :
    S.subtype ≃ S.reflect.subtype := Equiv.ofBijective
  (fun x => ⟨-(x : ℝ), ⟨x, x.property, rfl⟩⟩)
  (by
    constructor
    · intro x y he
      apply Subtype.ext
      exact neg_injective (congrArg Subtype.val he)
    · rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩)

theorem LocallyFiniteCarrier.reflectionEquiv_val (S : LocallyFiniteCarrier) (x : S.subtype) :
    (S.reflectionEquiv x : ℝ) = -(x : ℝ) := rfl

/-- Physical reflection as the genuine Schwartz pushforward operator. -/
def originalDistributionReflection :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  combDistributionDilation (-1) (by norm_num)

theorem originalDistributionReflection_apply (T : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) :
    originalDistributionReflection T f = T (combSchwartzDilation (-1) (by norm_num) f) := rfl

/-- Genuine Fourier inversion supplies the full actual reflection, not a support-only rule. -/
theorem fourier_fourier_eq_originalDistributionReflection (T : TemperedDistribution ℝ ℂ) :
    𝓕 (𝓕 T) = originalDistributionReflection T := by
  ext f
  rw [TemperedDistribution.fourier_apply, TemperedDistribution.fourier_apply,
    originalDistributionReflection_apply]
  congr 1
  ext x
  have hi : (𝓕⁻ (𝓕 f) : SchwartzMap ℝ ℂ) = f := FourierTransform.fourierInv_fourier_eq f
  have h := congrArg (fun g : SchwartzMap ℝ ℂ => g (-x)) hi
  change (𝓕 (𝓕 f)) (-(-x)) = f (-x) at h
  rw [neg_neg] at h
  simpa only [combSchwartzDilation_apply, neg_one_mul] using h

/-- Reflection preserves actual local atomicity on the COMPLETE geometric carrier. -/
theorem atomicOnCarrier_originalDistributionReflection (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T) :
    AtomicOnCarrier S.reflect (originalDistributionReflection T) := by
  intro f hf
  rw [originalDistributionReflection_apply]
  apply hT
  intro x hx
  rw [combSchwartzDilation_apply, neg_one_mul]
  exact hf _ ⟨x, hx, rfl⟩

/-- Every original reflection coefficient equals its actual unreflected isolation action. -/
theorem originalDistributionReflection_isolation_apply (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T) (x : S.subtype) :
    originalDistributionReflection T (S.reflect.isolationSchwartz (S.reflectionEquiv x)) =
      T (S.isolationSchwartz x) := by
  have hz : SchwartzVanishesOn S
      (combSchwartzDilation (-1) (by norm_num)
        (S.reflect.isolationSchwartz (S.reflectionEquiv x)) - S.isolationSchwartz x) := by
    intro y hy
    let yS : S.subtype := ⟨y, hy⟩
    rw [sub_apply, combSchwartzDilation_apply, neg_one_mul]
    apply sub_eq_zero.mpr
    change S.reflect.isolationSchwartz (S.reflectionEquiv x)
      (S.reflectionEquiv yS) = S.isolationSchwartz x yS
    simp only [LocallyFiniteCarrier.isolationSchwartz_apply_subtype,
      S.reflectionEquiv.injective.eq_iff]
  have he := (hasLocallyAtomicAction_atomicOnCarrier S T hT) _ hz
  rw [map_sub, sub_eq_zero] at he
  exact he

/-- ALL original reflection masses agree exactly at the SAME exponent. -/
theorem stronglyTemperedCoefficientTerm_reflection_eq (S : LocallyFiniteCarrier)
    (N : ℕ) (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T) (x : S.subtype) :
    stronglyTemperedCoefficientTerm S.reflect N (originalDistributionReflection T)
      (S.reflectionEquiv x) = stronglyTemperedCoefficientTerm S N T x := by
  unfold stronglyTemperedCoefficientTerm
  rw [originalDistributionReflection_isolation_apply S T hT x, S.reflectionEquiv_val, abs_neg]

/-- Actual Fourier square preserves the original SAME-exponent weighted-TV record under reflection. -/
theorem stronglyTemperedAtomicAtExponent_fourier_fourier (S : LocallyFiniteCarrier)
    (N : ℕ) (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    𝓕 (𝓕 T) ∈ stronglyTemperedAtomicAtExponent S.reflect N := by
  rw [fourier_fourier_eq_originalDistributionReflection]
  refine ⟨atomicOnCarrier_hasLocallyAtomicAction _ _
    (atomicOnCarrier_originalDistributionReflection S T
      (hasLocallyAtomicAction_atomicOnCarrier S T hT.1)), ?_⟩
  rw [← S.reflectionEquiv.summable_iff]
  have he : (fun x => stronglyTemperedCoefficientTerm S.reflect N
      (originalDistributionReflection T) (S.reflectionEquiv x)) =
      stronglyTemperedCoefficientTerm S N T :=
    funext (stronglyTemperedCoefficientTerm_reflection_eq S N T hT.1)
  change Summable (fun x => stronglyTemperedCoefficientTerm S.reflect N
    (originalDistributionReflection T) (S.reflectionEquiv x))
  rw [he]
  exact hT.2

end
end MeyerGeneralProblem
