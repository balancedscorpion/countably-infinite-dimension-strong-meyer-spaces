module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.PhysicalDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductResidues

@[expose] public section

/-! Original PhysicalDistribution for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The actual physical residue distribution on the COMPLETE original product carrier. -/
def productPhysicalDistribution {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    TemperedDistribution ℝ ℂ :=
  weightedAtomicDistribution (compactOriginalProductSheetCarrier block) (productPhysicalResidue block r)
    ((s - 1) + 2) (productPhysicalResidue_weight_summable block r)

theorem productPhysicalDistribution_apply {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (f : SchwartzMap ℝ ℂ) :
    productPhysicalDistribution block r f =
      ∑' x : (compactOriginalProductSheetCarrier block).subtype, productPhysicalResidue block r x * f x := rfl

theorem productPhysicalDistribution_atomicOnCarrier {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    AtomicOnCarrier (compactOriginalProductSheetCarrier block) (productPhysicalDistribution block r) :=
  weightedAtomicDistribution_atomicOnCarrier _ _ _ _

theorem productPhysicalDistribution_isLocallyAtomicCoefficientFamily
    {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    IsLocallyAtomicCoefficientFamily (compactOriginalProductSheetCarrier block)
      (productPhysicalDistribution block r) (productPhysicalResidue block r) :=
  weightedAtomicDistribution_isLocallyAtomicCoefficientFamily _ _ _ _

theorem productPhysicalDistribution_isolation {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : (compactOriginalProductSheetCarrier block).subtype) :
    productPhysicalDistribution block r ((compactOriginalProductSheetCarrier block).isolationSchwartz x) =
      productPhysicalResidue block r x := weightedAtomicDistribution_isolation _ _ _ _ _

/-- Actual original physical strong admission at a proved, explicit exponent. -/
theorem productPhysicalDistribution_mem_strongExponent {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    productPhysicalDistribution block r ∈
      stronglyTemperedAtomicAtExponent (compactOriginalProductSheetCarrier block) ((s - 1) + 2) :=
  weightedAtomicDistribution_mem_strongExponent _ _ _ _

theorem productPhysicalDistribution_mem_strongAtomic {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    productPhysicalDistribution block r ∈ StronglyTemperedAtomicOnCarrier (compactOriginalProductSheetCarrier block) := by
  apply (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
  exact ⟨(s - 1) + 2, productPhysicalDistribution_mem_strongExponent block r⟩

theorem productPhysicalResidue_add {s : ℕ} (block : CompactOriginalParameterBlock s) (r t : productNumeratorIndex s → ℂ)
    (x : (compactOriginalProductSheetCarrier block).subtype) :
    productPhysicalResidue block (r + t) x =
      productPhysicalResidue block r x + productPhysicalResidue block t x := by
  unfold productPhysicalResidue productSlabNumerator
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_add, add_div]

theorem productPhysicalResidue_smul {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (c : ℂ) (x : (compactOriginalProductSheetCarrier block).subtype) :
    productPhysicalResidue block (c • r) x = c • productPhysicalResidue block r x := by
  unfold productPhysicalResidue productSlabNumerator
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem productPhysicalDistribution_add {s : ℕ} (block : CompactOriginalParameterBlock s) (r t : productNumeratorIndex s → ℂ) :
    productPhysicalDistribution block (r + t) =
      productPhysicalDistribution block r + productPhysicalDistribution block t := by
  ext f
  change productPhysicalDistribution block (r + t) f =
    productPhysicalDistribution block r f + productPhysicalDistribution block t f
  simp only [productPhysicalDistribution_apply, productPhysicalResidue_add, add_mul]
  exact Summable.tsum_add
    (weightedAtomic_samples_summable _ _ _ (productPhysicalResidue_weight_summable block r) f)
    (weightedAtomic_samples_summable _ _ _ (productPhysicalResidue_weight_summable block t) f)

theorem productPhysicalDistribution_smul {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) (c : ℂ) :
    productPhysicalDistribution block (c • r) = c • productPhysicalDistribution block r := by
  ext f
  change productPhysicalDistribution block (c • r) f = c * productPhysicalDistribution block r f
  simp only [productPhysicalDistribution_apply, productPhysicalResidue_smul, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

/-- The literal slab-to-physical-distribution map is complex linear. -/
def productPhysicalDistributionLinearMap {s : ℕ} (block : CompactOriginalParameterBlock s) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toFun := productPhysicalDistribution block
  map_add' := productPhysicalDistribution_add block
  map_smul' := fun c r => productPhysicalDistribution_smul block r c

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
