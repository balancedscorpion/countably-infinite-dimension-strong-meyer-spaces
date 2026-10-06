module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixCosets
public import MeyerGeneralProblem.Distribution.ReflectionSupportRecovery

@[expose] public section

/-! Subtraction recovers the genuine companion cone/root pair for EVERY
actual original strong mixed-prefix pair. Nonmodule reflected-root cosets are
eliminated by the actual nonzero motif, before literal identification. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The genuine physical remainder is atomic on the FULL root/cone union. -/
theorem originalScheduledPrefixRootSource_complement_atomicOnUnion (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    AtomicOnCarrier ((originalScheduledPrefixFullRootCarrier bound k).union
      (originalScheduledPrefixCone bound k)) (T - originalScheduledPrefixRootSource bound k N T hF) := by
  have hTU : AtomicOnCarrier ((originalScheduledPrefixFullRootCarrier bound k).union
      (originalScheduledPrefixCone bound k)) T := (hasLocallyAtomicAction_atomicOnCarrier _ T hT.1).mono
    (originalScheduledPrefixCarrier_subset_roots_union_cone bound k)
  have hρU : AtomicOnCarrier ((originalScheduledPrefixFullRootCarrier bound k).union
      (originalScheduledPrefixCone bound k)) (originalScheduledPrefixRootSource bound k N T hF) :=
    (originalScheduledPrefixRootSource_atomicOnRoots bound k M N T hT hF).mono
    (Set.subset_union_left : (originalScheduledPrefixFullRootCarrier bound k).carrier ⊆
      ((originalScheduledPrefixFullRootCarrier bound k).union (originalScheduledPrefixCone bound k)).carrier)
  intro f hf
  change T f - originalScheduledPrefixRootSource bound k N T hF f = 0
  rw [hTU f hf, hρU f hf, sub_self]

/-- The actual double Fourier remainder is supported on full reflected roots and the whole cone. -/
theorem originalScheduledPrefixRootSource_complement_fourier_fourier_atomicOnUnion
    (bound : ℕ → ℕ) (k M N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    AtomicOnCarrier ((originalScheduledPrefixFullRootCarrier bound k).reflect.union
      (originalScheduledPrefixCone bound k)) (𝓕 (𝓕 (T - originalScheduledPrefixRootSource bound k N T hF))) := by
  rw [fourier_fourier_eq_originalDistributionReflection]
  apply (atomicOnCarrier_originalDistributionReflection _ _
    (originalScheduledPrefixRootSource_complement_atomicOnUnion bound k M N T hT hF)).mono
  rintro x ⟨y, hy, rfl⟩
  rcases hy with hy | hy
  · exact Or.inl ⟨y, hy, rfl⟩
  · exact Or.inr ((originalScheduledPrefixCone_neg_iff bound k y).mpr hy)

/-- ALL off-cone original rows of the double Fourier remainder vanish; every
reflected complete root has its singleton integer-module coset checked. -/
theorem originalScheduledPrefixRootSource_complement_fourier_fourier_atomicOnCone
    (bound : ℕ → ℕ) (k M N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    AtomicOnCarrier (originalScheduledPrefixCone bound k)
      (𝓕 (𝓕 (T - originalScheduledPrefixRootSource bound k N T hF))) := by
  classical
  let U := (originalScheduledPrefixFullRootCarrier bound k).reflect.union (originalScheduledPrefixCone bound k)
  let P := 𝓕 (𝓕 (T - originalScheduledPrefixRootSource bound k N T hF))
  have hP : AtomicOnCarrier U P :=
    originalScheduledPrefixRootSource_complement_fourier_fourier_atomicOnUnion bound k M N T hT hF
  have ha : (fun i : OriginalScheduledPrefixMotif bound k => originalScaledModuleFrequencyHom
      (originalPrivateScale (originalScheduledPrefixDenominator bound k))
      (originalPositivePolynomialIntegerCoordinates (originalScheduledPrefixPolynomialCoordinates bound k) i)) =
      originalPositivePolynomialFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k))
        (originalScheduledPrefixPolynomialCoordinates bound k) :=
    funext (originalScheduledPrefixMotifFrequency_eq bound k)
  have hzero : finiteCombConvolution (fun i : OriginalScheduledPrefixMotif bound k =>
      originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k))
        (originalPositivePolynomialIntegerCoordinates (originalScheduledPrefixPolynomialCoordinates bound k) i))
      (originalScheduledPrefixPolynomialCoefficient bound k) P = 0 := by
    rw [ha]
    apply finiteCombConvolution_fourier_eq_zero (originalScheduledPrefixFullRootCarrier bound k) _
      (originalScheduledPrefixRootSource_complement_fourier_atomicOnRoots bound k N T hF)
    intro x hx
    exact originalScheduledPrefixPolynomial_vanishes bound k x hx
  have hrestricted : AtomicOnCarrier (U.restrict (originalScheduledPrefixCone bound k).carrier
      Set.subset_union_right) P := by
    apply (atomicOnCarrier_restrict_iff U _ Set.subset_union_right P).mpr
    refine ⟨hP, ?_⟩
    intro x hx
    have hroot : (x : ℝ) ∈ (originalScheduledPrefixFullRootCarrier bound k).reflect.carrier :=
      x.property.resolve_right hx
    let i : OriginalScheduledPrefixMotif bound k := Classical.choice (originalScheduledPrefixMotif_nonempty bound k)
    have hz := extendedAtomicCoefficient_eq_zero_of_singleton_module_coset U
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
      (originalPositivePolynomialIntegerCoordinates (originalScheduledPrefixPolynomialCoordinates bound k))
      (originalScheduledPrefixPolynomialCoefficient bound k)
      (originalScheduledPrefixMotifFrequency_injective bound k) i
      (originalScheduledPrefixMotifCoefficient_ne_zero bound k i) P hP hzero x
      (originalScheduledPrefixReflectedRoot_singleton_coset bound k x hroot)
    unfold extendedAtomicCoefficient at hz
    rw [dite_eq_left (show (x : ℝ) ∈ U.carrier from x.property)] at hz
    exact hz
  exact hrestricted.mono (fun _ hx => hx)

/-- The actual physical remainder is on the cone: a GENUINE companion cone/root Fourier pair. -/
theorem originalScheduledPrefixRootSource_complement_atomicOnCone (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    AtomicOnCarrier (originalScheduledPrefixCone bound k)
      (T - originalScheduledPrefixRootSource bound k N T hF) := by
  apply atomicOnCarrier_of_originalDistributionReflection (originalScheduledPrefixCone bound k)
    (fun x hx => (originalScheduledPrefixCone_neg_iff bound k x).mpr hx)
  rw [← fourier_fourier_eq_originalDistributionReflection]
  exact originalScheduledPrefixRootSource_complement_fourier_fourier_atomicOnCone bound k M N T hT hF

end
end MeyerGeneralProblem.StrongParity
