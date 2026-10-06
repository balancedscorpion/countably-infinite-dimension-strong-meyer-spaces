module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.PhysicalDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductFourierPair
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPairClassification
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductResidues
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralConeIndex
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductOriginalRows

@[expose] public section

/-! Complete original ProductOriginalRows for actual compact parameter blocks.
Every original supported pair is retained, without a constructed-image premise. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open scoped FourierTransform

/-- Evaluation of the literal original slab at an actual full product root. -/
def productOriginalPhysicalRow {s : ℕ} (block : CompactOriginalParameterBlock s) (x : (compactOriginalProductSheetCarrier block).subtype) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ where
  toFun r := productSlabNumerator s r x
  map_add' r t := by
    simp only [productSlabNumerator, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c r := by
    simp only [productSlabNumerator, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_assoc, ← Finset.mul_sum]

/-- The ORIGINAL Fourier coefficient of the actual source, recovered by the
complete cone's actual isolation test, not by an assumed Taylor row. -/
def productOriginalSpectralRow {s : ℕ} (block : CompactOriginalParameterBlock s) (x : spectralConeCarrier.subtype) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ where
  toFun r := 𝓕 (productPhysicalDistribution block r) (spectralConeCarrier.isolationSchwartz x)
  map_add' r t := by
    rw [productPhysicalDistribution_add, FourierTransform.fourier_add]
    rfl
  map_smul' c r := by
    rw [productPhysicalDistribution_smul, FourierTransform.fourier_smul]
    rfl

theorem productOriginalSpectralRow_eq_coefficient {s : ℕ} (block : CompactOriginalParameterBlock s)
    (x : spectralConeCarrier.subtype) (r : productNumeratorIndex s → ℂ) :
    productOriginalSpectralRow block x r = productSpectralCoefficient block r x := by
  change 𝓕 (productPhysicalDistribution block r) (spectralConeCarrier.isolationSchwartz x) = _
  rw [productPhysical_fourier_eq_spectral, productSpectralDistribution_isolation]

theorem productSheetTorusDerivative_ne_zero_at_root {s : ℕ} (block : CompactOriginalParameterBlock s)
    (x : (compactOriginalProductSheetCarrier block).subtype) :
    compactOriginalSheetTorusDerivative block (unitPhase x) (unitPhase (beta * x - 1 / 4)) ≠ 0 := by
  have hr : compactOriginalComplexSheetProduct block (x : ℂ) = 0 := by
    rw [compactOriginalComplexSheetProduct_ofReal]
    exact x.property
  have hd := compactOriginalComplexSheetProduct_deriv_ne_zero block hr
  rw [(compactOriginalComplexSheetProduct_torus_hasDerivAt block (x : ℂ)).deriv] at hd
  have h := (mul_ne_zero_iff.mp hd).2
  have hw : (beta : ℂ) * (x : ℂ) - 1 / 4 = ((beta * x - 1 / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  simpa only [hw, complexUnitPhase_ofReal] using h

theorem productPhysicalResidue_eq_zero_iff {s : ℕ} (block : CompactOriginalParameterBlock s)
    (r : productNumeratorIndex s → ℂ) (x : (compactOriginalProductSheetCarrier block).subtype) :
    productPhysicalResidue block r x = 0 ↔ productOriginalPhysicalRow block x r = 0 := by
  unfold productPhysicalResidue
  rw [div_eq_zero_iff]
  simp only [productSheetTorusDerivative_ne_zero_at_root block x, or_false, neg_eq_zero]
  rfl

/-- Actual root evaluations separate the complete original finite slab,
using actual physical residues and the proved original inverse injection. -/
theorem productOriginalPhysicalRows_separate {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (hr : ∀ x : (compactOriginalProductSheetCarrier block).subtype, productOriginalPhysicalRow block x r = 0) :
    r = 0 := by
  have hT : productPhysicalDistribution block r = 0 := by
    ext f
    rw [productPhysicalDistribution_apply]
    calc
      _ = ∑' _x : (compactOriginalProductSheetCarrier block).subtype, (0 : ℂ) := by
        apply tsum_congr
        intro x
        rw [(productPhysicalResidue_eq_zero_iff block r x).mpr (hr x), zero_mul]
      _ = 0 := tsum_zero
  apply productPhysicalDistribution_injective block
  exact hT.trans (productPhysicalDistributionLinearMap block).map_zero.symm

/-- Every original forbidden physical and Fourier point, indexed once. -/
def productOriginalDeletionIndex {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :=
  {x : (compactOriginalProductSheetCarrier block).subtype // (x : ℝ) ∈ E} ⊕
    {x : spectralConeCarrier.subtype // (x : ℝ) ∈ F}

/-- The full family of ORIGINAL deletion rows, not a selected subsystem. -/
def productOriginalDeletionRow {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    productOriginalDeletionIndex block E F → (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ
  | .inl x => productOriginalPhysicalRow block x.val
  | .inr x => productOriginalSpectralRow block x.val

/-- The complete simultaneous kernel of every original support deletion. -/
def productOriginalDeletionKernel {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    Submodule ℂ (productNumeratorIndex s → ℂ) :=
  UniformDiscrete.rowKernel (productOriginalDeletionRow block E F)

theorem mem_productOriginalDeletionKernel_iff {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ)
    (r : productNumeratorIndex s → ℂ) :
    r ∈ productOriginalDeletionKernel block E F ↔
      (∀ x : (compactOriginalProductSheetCarrier block).subtype, (x : ℝ) ∈ E → productOriginalPhysicalRow block x r = 0) ∧
      (∀ x : spectralConeCarrier.subtype, (x : ℝ) ∈ F → productOriginalSpectralRow block x r = 0) := by
  constructor
  · intro h
    exact ⟨fun x hx => h (.inl ⟨x, hx⟩), fun x hx => h (.inr ⟨x, hx⟩)⟩
  · rintro ⟨hE, hF⟩ (x | x)
    · exact hE x.val x.property
    · exact hF x.val x.property

/-- The COMPLETE original deleted root/cone directed pair space. -/
def productOriginalDeletedPairSpace {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  schwartzAnnihilator (schwartzVanishingSubmodule ((compactOriginalProductSheetCarrier block).delete E)) ⊓
    (schwartzAnnihilator (schwartzVanishingSubmodule (spectralConeCarrier.delete F))).comap
      temperedFourierLinearMap

theorem productPhysical_mem_deletedPairSpace_iff {s : ℕ} (block : CompactOriginalParameterBlock s) (E F : Set ℝ)
    (r : productNumeratorIndex s → ℂ) :
    productPhysicalDistribution block r ∈ productOriginalDeletedPairSpace block E F ↔
      r ∈ productOriginalDeletionKernel block E F := by
  change AtomicOnCarrier ((compactOriginalProductSheetCarrier block).delete E) (productPhysicalDistribution block r) ∧
    AtomicOnCarrier (spectralConeCarrier.delete F) (𝓕 (productPhysicalDistribution block r)) ↔ _
  rw [atomicOnCarrier_delete_iff, atomicOnCarrier_delete_iff,
    mem_productOriginalDeletionKernel_iff]
  have hT := productPhysicalDistribution_atomicOnCarrier block r
  have hFT : AtomicOnCarrier spectralConeCarrier (𝓕 (productPhysicalDistribution block r)) := by
    rw [productPhysical_fourier_eq_spectral]
    exact productSpectralDistribution_atomicOnCarrier block r
  simp only [hT, hFT, true_and, productPhysicalDistribution_isolation,
    productPhysicalResidue_eq_zero_iff]
  rfl

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
