module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductResidues
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductPoleMass
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.PhysicalDistribution

@[expose] public section

/-! Original ProductPoleMass for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The literal original meromorphic quotient, with the entire product denominator. -/
def complexProductSlabQuotient {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) (z : ℂ) : ℂ :=
  complexProductSlabNumerator s r z / compactOriginalComplexSheetProduct block z

/-- The actual quotient's simple-pole coefficient at every complete original root. -/
def productPoleResidue {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : (compactOriginalProductSheetCarrier block).subtype) : ℂ :=
  complexProductSlabNumerator s r x / deriv (compactOriginalComplexSheetProduct block) x

/-- The literal continuous principal-part remainder at an original root. -/
def productPoleRemainder {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : (compactOriginalProductSheetCarrier block).subtype) : ℂ → ℂ :=
  simplePoleRemainder (compactOriginalComplexSheetProduct block) (complexProductSlabNumerator s r) x

theorem productPoleRemainder_continuousAt {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : (compactOriginalProductSheetCarrier block).subtype) : ContinuousAt (productPoleRemainder block r x) (x : ℂ) := by
  have hroot : compactOriginalComplexSheetProduct block (x : ℂ) = 0 := by
    rw [compactOriginalComplexSheetProduct_ofReal block]
    exact x.property
  apply simplePoleRemainder_continuousAt
  · intro z
    exact (compactOriginalComplexSheetProduct_hasDerivAt block z).differentiableAt
  · exact complexProductSlabNumerator_differentiable s r (x : ℂ)
  · exact compactOriginalComplexSheetProduct_deriv_ne_zero block hroot

theorem complexProductSlabQuotient_principal_part {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : (compactOriginalProductSheetCarrier block).subtype) {z : ℂ} (hz : z ≠ (x : ℂ)) :
    complexProductSlabQuotient block r z =
      productPoleResidue block r x / (z - (x : ℂ)) + productPoleRemainder block r x z := by
  exact simplePoleRemainder_identity (compactOriginalComplexSheetProduct block) (complexProductSlabNumerator s r)
    (x : ℂ) (by rw [compactOriginalComplexSheetProduct_ofReal block]; exact x.property) hz

/-- The negative-exponential Fourier jump gives EXACTLY the original physical residue. -/
theorem productPoleResidue_original_mass {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : (compactOriginalProductSheetCarrier block).subtype) :
    -((2 * Real.pi : ℝ) * Complex.I) * productPoleResidue block r x = productPhysicalResidue block r x := by
  have hC : (2 * Real.pi : ℝ) * Complex.I ≠ (0 : ℂ) := by
    apply mul_ne_zero
    · exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
    · exact Complex.I_ne_zero
  have hd : deriv (compactOriginalComplexSheetProduct block) (x : ℂ) =
      (2 * Real.pi : ℝ) * Complex.I * compactOriginalSheetTorusDerivative block
        (unitPhase x) (unitPhase (beta * x - 1 / 4)) := by
    rw [(compactOriginalComplexSheetProduct_torus_hasDerivAt block (x : ℂ)).deriv,
      complexUnitPhase_ofReal,
      show (beta : ℂ) * (x : ℂ) - 1 / 4 = (beta * x - 1 / 4 : ℝ) by push_cast; ring,
      complexUnitPhase_ofReal]
  have hroot : compactOriginalComplexSheetProduct block (x : ℂ) = 0 := by
    rw [compactOriginalComplexSheetProduct_ofReal block]
    exact x.property
  have hG : compactOriginalSheetTorusDerivative block (unitPhase x)
      (unitPhase (beta * x - 1 / 4)) ≠ 0 := by
    have h := compactOriginalComplexSheetProduct_deriv_ne_zero block hroot
    rw [hd] at h
    exact (mul_ne_zero_iff.mp h).2
  unfold productPoleResidue productPhysicalResidue
  rw [complexProductSlabNumerator_ofReal, hd]
  field_simp

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
