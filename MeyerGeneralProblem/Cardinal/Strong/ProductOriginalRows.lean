module

public import MeyerGeneralProblem.Cardinal.Strong.ProductPairClassification
public import MeyerGeneralProblem.Distribution.RestrictedAtomicRows
public import MeyerGeneralProblem.UniformDiscrete.FiniteRows

@[expose] public section

/-! Actual original physical evaluation and Fourier coefficient rows on the
complete slab. Their full kernel is precisely the directed deleted-support
condition, using the actual original denominator, signs and quarter phases. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped FourierTransform

/-- Evaluation of the literal original slab at an actual full product root. -/
def productOriginalPhysicalRow (s : ℕ) (x : (productSheetCarrier s).subtype) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ where
  toFun r := productSlabNumerator s r x
  map_add' r t := by
    simp only [productSlabNumerator, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c r := by
    simp only [productSlabNumerator, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_assoc, ← Finset.mul_sum]

/-- The ORIGINAL Fourier coefficient of the actual source, recovered by the
complete cone's actual isolation test, not by an assumed Taylor row. -/
def productOriginalSpectralRow (s : ℕ) (x : spectralConeCarrier.subtype) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ where
  toFun r := 𝓕 (productPhysicalDistribution s r) (spectralConeCarrier.isolationSchwartz x)
  map_add' r t := by
    rw [productPhysicalDistribution_add, FourierTransform.fourier_add]
    rfl
  map_smul' c r := by
    rw [productPhysicalDistribution_smul, FourierTransform.fourier_smul]
    rfl

theorem productOriginalSpectralRow_eq_coefficient (s : ℕ)
    (x : spectralConeCarrier.subtype) (r : productNumeratorIndex s → ℂ) :
    productOriginalSpectralRow s x r = productSpectralCoefficient s r x := by
  change 𝓕 (productPhysicalDistribution s r) (spectralConeCarrier.isolationSchwartz x) = _
  rw [productPhysical_fourier_eq_spectral, productSpectralDistribution_isolation]

theorem productSheetTorusDerivative_ne_zero_at_root (s : ℕ)
    (x : (productSheetCarrier s).subtype) :
    productSheetTorusDerivative s (unitPhase x) (unitPhase (beta * x - 1 / 4)) ≠ 0 := by
  have hr : complexSheetProduct s (x : ℂ) = 0 := by
    rw [complexSheetProduct_ofReal]
    exact x.property
  have hd := complexSheetProduct_deriv_ne_zero s hr
  rw [(complexSheetProduct_torus_hasDerivAt s (x : ℂ)).deriv] at hd
  have h := (mul_ne_zero_iff.mp hd).2
  have hw : (beta : ℂ) * (x : ℂ) - 1 / 4 = ((beta * x - 1 / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  simpa only [hw, complexUnitPhase_ofReal] using h

theorem productPhysicalResidue_eq_zero_iff (s : ℕ)
    (r : productNumeratorIndex s → ℂ) (x : (productSheetCarrier s).subtype) :
    productPhysicalResidue s r x = 0 ↔ productOriginalPhysicalRow s x r = 0 := by
  unfold productPhysicalResidue
  rw [div_eq_zero_iff]
  simp only [productSheetTorusDerivative_ne_zero_at_root s x, or_false, neg_eq_zero]
  rfl

/-- Actual root evaluations separate the complete original finite slab,
using actual physical residues and the proved original inverse injection. -/
theorem productOriginalPhysicalRows_separate (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (hr : ∀ x : (productSheetCarrier s).subtype, productOriginalPhysicalRow s x r = 0) :
    r = 0 := by
  have hT : productPhysicalDistribution s r = 0 := by
    ext f
    rw [productPhysicalDistribution_apply]
    calc
      _ = ∑' _x : (productSheetCarrier s).subtype, (0 : ℂ) := by
        apply tsum_congr
        intro x
        rw [(productPhysicalResidue_eq_zero_iff s r x).mpr (hr x), zero_mul]
      _ = 0 := tsum_zero
  apply productPhysicalDistribution_injective s
  exact hT.trans (productPhysicalDistributionLinearMap s).map_zero.symm

/-- Every original forbidden physical and Fourier point, indexed once. -/
def productOriginalDeletionIndex (s : ℕ) (E F : Set ℝ) :=
  {x : (productSheetCarrier s).subtype // (x : ℝ) ∈ E} ⊕
    {x : spectralConeCarrier.subtype // (x : ℝ) ∈ F}

/-- The full family of ORIGINAL deletion rows, not a selected subsystem. -/
def productOriginalDeletionRow (s : ℕ) (E F : Set ℝ) :
    productOriginalDeletionIndex s E F → (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ
  | .inl x => productOriginalPhysicalRow s x.val
  | .inr x => productOriginalSpectralRow s x.val

/-- The complete simultaneous kernel of every original support deletion. -/
def productOriginalDeletionKernel (s : ℕ) (E F : Set ℝ) :
    Submodule ℂ (productNumeratorIndex s → ℂ) :=
  UniformDiscrete.rowKernel (productOriginalDeletionRow s E F)

theorem mem_productOriginalDeletionKernel_iff (s : ℕ) (E F : Set ℝ)
    (r : productNumeratorIndex s → ℂ) :
    r ∈ productOriginalDeletionKernel s E F ↔
      (∀ x : (productSheetCarrier s).subtype, (x : ℝ) ∈ E → productOriginalPhysicalRow s x r = 0) ∧
      (∀ x : spectralConeCarrier.subtype, (x : ℝ) ∈ F → productOriginalSpectralRow s x r = 0) := by
  constructor
  · intro h
    exact ⟨fun x hx => h (.inl ⟨x, hx⟩), fun x hx => h (.inr ⟨x, hx⟩)⟩
  · rintro ⟨hE, hF⟩ (x | x)
    · exact hE x.val x.property
    · exact hF x.val x.property

/-- The COMPLETE original deleted root/cone directed pair space. -/
def productOriginalDeletedPairSpace (s : ℕ) (E F : Set ℝ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  schwartzAnnihilator (schwartzVanishingSubmodule ((productSheetCarrier s).delete E)) ⊓
    (schwartzAnnihilator (schwartzVanishingSubmodule (spectralConeCarrier.delete F))).comap
      temperedFourierLinearMap

theorem productPhysical_mem_deletedPairSpace_iff (s : ℕ) (E F : Set ℝ)
    (r : productNumeratorIndex s → ℂ) :
    productPhysicalDistribution s r ∈ productOriginalDeletedPairSpace s E F ↔
      r ∈ productOriginalDeletionKernel s E F := by
  change AtomicOnCarrier ((productSheetCarrier s).delete E) (productPhysicalDistribution s r) ∧
    AtomicOnCarrier (spectralConeCarrier.delete F) (𝓕 (productPhysicalDistribution s r)) ↔ _
  rw [atomicOnCarrier_delete_iff, atomicOnCarrier_delete_iff,
    mem_productOriginalDeletionKernel_iff]
  have hT := productPhysicalDistribution_atomicOnCarrier s r
  have hFT : AtomicOnCarrier spectralConeCarrier (𝓕 (productPhysicalDistribution s r)) := by
    rw [productPhysical_fourier_eq_spectral]
    exact productSpectralDistribution_atomicOnCarrier s r
  simp only [hT, hFT, true_and, productPhysicalDistribution_isolation,
    productPhysicalResidue_eq_zero_iff]
  rfl

end

end MeyerGeneralProblem.StrongParity
