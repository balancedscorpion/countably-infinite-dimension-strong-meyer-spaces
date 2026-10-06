module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixSimpleRoots
public import MeyerGeneralProblem.Distribution.OriginalWeightedAtomicRestriction
public import MeyerGeneralProblem.Distribution.ModuleAtomicAnnihilation

@[expose] public section

/-! The genuine spectral module record of EVERY actual original strong pair.
It is built from the ORIGINAL FT isolation coefficients, retaining the SAME
weighted exponent. Whole module recurrence gives a genuine zero convolution;
no Fourier-admissible restriction or root-source certificate is assumed. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The actual entire common integer module, not a restriction to nonzero coefficients. -/
def originalScheduledPrefixModuleSet (bound : ℕ → ℕ) (k : ℕ) : Set ℝ :=
  Set.range (originalScaledModuleFrequencyHom
    (originalPrivateScale (originalScheduledPrefixDenominator bound k)))

/-- Every whole common-cone point has an actual integer module label. -/
theorem originalScheduledPrefixCone_subset_module (bound : ℕ → ℕ) (k : ℕ) :
    (originalScheduledPrefixCone bound k).carrier ⊆ originalScheduledPrefixModuleSet bound k := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨p, q, hy, _⟩ := (translatedConeSet_iff 0 0 y).mp hy
  refine ⟨(p, q), ?_⟩
  simp only [originalScaledModuleFrequencyHom_apply, originalScaledModuleFrequency, hy,
    Prod.fst, Prod.snd, div_eq_mul_inv, mul_comm]

/-- Every common integer module point lies in the paid full rational coarse module. -/
theorem originalScheduledPrefixModuleSet_subset_rational_module (bound : ℕ → ℕ) (k : ℕ) :
    originalScheduledPrefixModuleSet bound k ⊆ parityRationalCoarseModule := by
  rintro x ⟨z, rfl⟩
  exact originalScaledModuleFrequency_mem_rational_module _ (originalScheduledPrefixDenominator_pos bound k) z

/-- The actual weighted original module spectral record as a genuine tempered distribution. -/
def originalScheduledPrefixModuleSpectralRecord (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    TemperedDistribution ℝ ℂ :=
  originalWeightedAtomicRestriction (originalScheduledPrefixCarrier bound k)
    (originalScheduledPrefixModuleSet bound k) N (𝓕 T) hF

/-- The genuine module record retains weighted original spectral variation at the SAME N. -/
theorem originalScheduledPrefixModuleSpectralRecord_mem_strongExponent (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    originalScheduledPrefixModuleSpectralRecord bound k N T hF ∈
      stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N :=
  originalWeightedAtomicRestriction_mem_strongExponent _ _ _ _ _

/-- At EVERY module label, the genuine record has exactly the ORIGINAL Fourier coefficient. -/
theorem originalScheduledPrefixModuleSpectralRecord_coefficient (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N)
    (z : ℤ × ℤ) :
    extendedAtomicCoefficient (originalScheduledPrefixCarrier bound k)
      (originalScheduledPrefixModuleSpectralRecord bound k N T hF)
      (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z) =
        originalScheduledPrefixFourierArray bound k T z := by
  classical
  rw [originalScheduledPrefixModuleSpectralRecord, originalWeightedAtomicRestriction_extendedCoefficient]
  rw [ite_eq_left (show originalScaledModuleFrequencyHom
    (originalPrivateScale (originalScheduledPrefixDenominator bound k)) z ∈
      originalScheduledPrefixModuleSet bound k from ⟨z, rfl⟩)]
  rfl

/-- EVERY real point off the module has actual zero coefficient in the constructed record. -/
theorem originalScheduledPrefixModuleSpectralRecord_zero_off_module (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N)
    (x : ℝ) (hx : x ∉ originalScheduledPrefixModuleSet bound k) :
    extendedAtomicCoefficient (originalScheduledPrefixCarrier bound k)
      (originalScheduledPrefixModuleSpectralRecord bound k N T hF) x = 0 := by
  classical
  rw [originalScheduledPrefixModuleSpectralRecord, originalWeightedAtomicRestriction_extendedCoefficient,
    ite_eq_right hx]

/-- The genuine module record is atomic on the whole common cone, including axes and zero. -/
theorem originalScheduledPrefixModuleSpectralRecord_atomicOnCone (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    AtomicOnCarrier (originalScheduledPrefixCone bound k)
      (originalScheduledPrefixModuleSpectralRecord bound k N T hF) := by
  apply (originalWeightedAtomicRestriction_atomicOnCarrier _ _ _ _ hF).mono
  intro x hx
  rcases originalScheduledPrefixCarrier_subset_roots_union_cone bound k hx.1 with hroot | hcone
  · exact False.elim (originalScheduledPrefixRootSet_not_mem_module bound k x hroot
      (originalScheduledPrefixModuleSet_subset_rational_module bound k hx.2))
  · exact hcone

/-- The genuine complementary original spectral record is supported on the full root union. -/
theorem originalScheduledPrefixModuleSpectralRecord_complement_atomicOnRoots (bound : ℕ → ℕ) (k N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    AtomicOnCarrier (originalScheduledPrefixFullRootCarrier bound k)
      (𝓕 T - originalScheduledPrefixModuleSpectralRecord bound k N T hF) := by
  apply (originalWeightedAtomicRestriction_complement_atomicOnCarrier _ _ _ _ hF).mono
  intro x hx
  rcases originalScheduledPrefixCarrier_subset_roots_union_cone bound k hx.1 with hroot | hcone
  · exact hroot
  · exact False.elim (hx.2 (originalScheduledPrefixCone_subset_module bound k hcone))

/-- Every actual motif frequency is its literal positive integer module label. -/
theorem originalScheduledPrefixMotifFrequency_eq (bound : ℕ → ℕ) (k : ℕ)
    (i : OriginalScheduledPrefixMotif bound k) :
    originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k))
      (originalPositivePolynomialIntegerCoordinates (originalScheduledPrefixPolynomialCoordinates bound k) i) =
      originalPositivePolynomialFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k))
        (originalScheduledPrefixPolynomialCoordinates bound k) i := by
  simp only [originalScaledModuleFrequencyHom_apply, originalScaledModuleFrequency,
    originalPositivePolynomialIntegerCoordinates, originalPositivePolynomialFrequency, positiveConeFrequency,
    Prod.fst, Prod.snd, Int.cast_natCast]

/-- ALL module and nonmodule rows yield a genuinely zero convolution of the constructed record. -/
theorem originalScheduledPrefixModuleSpectralRecord_annihilated (bound : ℕ → ℕ) (k M N : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent (originalScheduledPrefixCarrier bound k) N) :
    finiteCombConvolution
      (originalPositivePolynomialFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k))
        (originalScheduledPrefixPolynomialCoordinates bound k))
      (originalScheduledPrefixPolynomialCoefficient bound k)
      (originalScheduledPrefixModuleSpectralRecord bound k N T hF) = 0 := by
  have ha : (fun i : OriginalScheduledPrefixMotif bound k => originalScaledModuleFrequencyHom
      (originalPrivateScale (originalScheduledPrefixDenominator bound k))
      (originalPositivePolynomialIntegerCoordinates (originalScheduledPrefixPolynomialCoordinates bound k) i)) =
      originalPositivePolynomialFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k))
        (originalScheduledPrefixPolynomialCoordinates bound k) :=
    funext (originalScheduledPrefixMotifFrequency_eq bound k)
  rw [← ha]
  apply finiteCombConvolution_eq_zero_of_module_recurrence (originalScheduledPrefixCarrier bound k) _ _ _ _
    (hasLocallyAtomicAction_atomicOnCarrier _ _
      (originalScheduledPrefixModuleSpectralRecord_mem_strongExponent bound k N T hF).1)
    (originalScheduledPrefixModuleSpectralRecord_zero_off_module bound k N T hF)
  intro z
  simp only [originalScheduledPrefixModuleSpectralRecord_coefficient]
  exact originalScheduledPrefix_all_integer_label_recurrence bound k M N T hT hF z

end
end MeyerGeneralProblem.StrongParity
