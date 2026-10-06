module

public import MeyerGeneralProblem.Cardinal.Strong.ProductResidues
public import MeyerGeneralProblem.Distribution.WeightedAtomic

@[expose] public section

/-!
# The actual strongly tempered physical record of every original slab numerator

The coefficient summability is already proved on the complete literal
product carrier. It now constructs an actual tempered distribution with
exact original physical residues as its isolation coefficients. No
spectral record or Fourier compatibility is presumed by this module.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The actual physical residue distribution on the COMPLETE original product carrier. -/
def productPhysicalDistribution (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    TemperedDistribution ℝ ℂ :=
  weightedAtomicDistribution (productSheetCarrier s) (productPhysicalResidue s r)
    ((s - 1) + 2) (productPhysicalResidue_weight_summable s r)

theorem productPhysicalDistribution_apply (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (f : SchwartzMap ℝ ℂ) :
    productPhysicalDistribution s r f =
      ∑' x : (productSheetCarrier s).subtype, productPhysicalResidue s r x * f x := rfl

theorem productPhysicalDistribution_atomicOnCarrier (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    AtomicOnCarrier (productSheetCarrier s) (productPhysicalDistribution s r) :=
  weightedAtomicDistribution_atomicOnCarrier _ _ _ _

theorem productPhysicalDistribution_isLocallyAtomicCoefficientFamily
    (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    IsLocallyAtomicCoefficientFamily (productSheetCarrier s)
      (productPhysicalDistribution s r) (productPhysicalResidue s r) :=
  weightedAtomicDistribution_isLocallyAtomicCoefficientFamily _ _ _ _

theorem productPhysicalDistribution_isolation (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : (productSheetCarrier s).subtype) :
    productPhysicalDistribution s r ((productSheetCarrier s).isolationSchwartz x) =
      productPhysicalResidue s r x := weightedAtomicDistribution_isolation _ _ _ _ _

/-- Actual original physical strong admission at a proved, explicit exponent. -/
theorem productPhysicalDistribution_mem_strongExponent (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    productPhysicalDistribution s r ∈
      stronglyTemperedAtomicAtExponent (productSheetCarrier s) ((s - 1) + 2) :=
  weightedAtomicDistribution_mem_strongExponent _ _ _ _

theorem productPhysicalDistribution_mem_strongAtomic (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    productPhysicalDistribution s r ∈ StronglyTemperedAtomicOnCarrier (productSheetCarrier s) := by
  apply (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr
  exact ⟨(s - 1) + 2, productPhysicalDistribution_mem_strongExponent s r⟩

theorem productPhysicalResidue_add (s : ℕ) (r t : productNumeratorIndex s → ℂ)
    (x : (productSheetCarrier s).subtype) :
    productPhysicalResidue s (r + t) x =
      productPhysicalResidue s r x + productPhysicalResidue s t x := by
  unfold productPhysicalResidue productSlabNumerator
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_add, add_div]

theorem productPhysicalResidue_smul (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (c : ℂ) (x : (productSheetCarrier s).subtype) :
    productPhysicalResidue s (c • r) x = c • productPhysicalResidue s r x := by
  unfold productPhysicalResidue productSlabNumerator
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem productPhysicalDistribution_add (s : ℕ) (r t : productNumeratorIndex s → ℂ) :
    productPhysicalDistribution s (r + t) =
      productPhysicalDistribution s r + productPhysicalDistribution s t := by
  ext f
  change productPhysicalDistribution s (r + t) f =
    productPhysicalDistribution s r f + productPhysicalDistribution s t f
  simp only [productPhysicalDistribution_apply, productPhysicalResidue_add, add_mul]
  exact Summable.tsum_add
    (weightedAtomic_samples_summable _ _ _ (productPhysicalResidue_weight_summable s r) f)
    (weightedAtomic_samples_summable _ _ _ (productPhysicalResidue_weight_summable s t) f)

theorem productPhysicalDistribution_smul (s : ℕ) (r : productNumeratorIndex s → ℂ) (c : ℂ) :
    productPhysicalDistribution s (c • r) = c • productPhysicalDistribution s r := by
  ext f
  change productPhysicalDistribution s (c • r) f = c * productPhysicalDistribution s r f
  simp only [productPhysicalDistribution_apply, productPhysicalResidue_smul, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

/-- The literal slab-to-physical-distribution map is complex linear. -/
def productPhysicalDistributionLinearMap (s : ℕ) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toFun := productPhysicalDistribution s
  map_add' := productPhysicalDistribution_add s
  map_smul' := fun c r => productPhysicalDistribution_smul s r c

end

end MeyerGeneralProblem.StrongParity
