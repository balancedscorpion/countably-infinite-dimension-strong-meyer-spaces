module

public import MeyerGeneralProblem.Cardinal.Strong.SimplePoleRemainder
public import MeyerGeneralProblem.Cardinal.Strong.PhysicalDistribution

@[expose] public section

/-! Actual pole remainders and their original physical masses.
All generic holomorphy and simple-zero hypotheses are discharged on the
literal complete finite product and every original slab numerator. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The complete original slab numerator on the actual entire quarter flow. -/
def complexProductSlabNumerator (s : ℕ) (r : productNumeratorIndex s → ℂ) (z : ℂ) : ℂ :=
  productSlabPolynomial s r (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4))

/-- The literal original meromorphic quotient, with the entire product denominator. -/
def complexProductSlabQuotient (s : ℕ) (r : productNumeratorIndex s → ℂ) (z : ℂ) : ℂ :=
  complexProductSlabNumerator s r z / complexSheetProduct s z

theorem productSheetPolynomial_onComplexFlow (s : ℕ) (z : ℂ) :
    productSheetPolynomial s (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4)) =
      complexSheetProduct s z := rfl

theorem complexSheetProduct_torus_hasDerivAt (s : ℕ) (z : ℂ) :
    HasDerivAt (complexSheetProduct s) ((2 * Real.pi : ℝ) * Complex.I *
      productSheetTorusDerivative s (complexUnitPhase z) (complexUnitPhase (beta * z - 1 / 4))) z := by
  convert! complexSheetProduct_hasDerivAt s z using 1
  unfold productSheetTorusDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [(complexSheetFlow_hasDerivAt (productSheetParameter s i) z).deriv]
  simp only [complexSheetFlow]
  ring

theorem complexProductSlabNumerator_differentiable (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    Differentiable ℂ (complexProductSlabNumerator s r) := by
  intro z
  have hZ := (complexUnitPhase_hasDerivAt z).differentiableAt
  have hinner : DifferentiableAt ℂ (fun w : ℂ => beta * w - 1 / 4) z := by fun_prop
  have hW := (complexUnitPhase_hasDerivAt (beta * z - 1 / 4)).differentiableAt.comp z hinner
  unfold complexProductSlabNumerator productSlabPolynomial
  apply DifferentiableAt.fun_sum
  intro ij _
  exact ((differentiableAt_const (r ij)).mul (hZ.pow (ij.val.1 : ℕ))).mul (hW.pow (ij.val.2 : ℕ))

theorem complexProductSlabNumerator_ofReal (s : ℕ) (r : productNumeratorIndex s → ℂ) (x : ℝ) :
    complexProductSlabNumerator s r x = productSlabNumerator s r x := by
  unfold complexProductSlabNumerator
  rw [complexUnitPhase_ofReal,
    show (beta : ℂ) * (x : ℂ) - 1 / 4 = (beta * x - 1 / 4 : ℝ) by push_cast; ring,
    complexUnitPhase_ofReal]
  rfl

/-- The actual quotient's simple-pole coefficient at every complete original root. -/
def productPoleResidue (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : (productSheetCarrier s).subtype) : ℂ :=
  complexProductSlabNumerator s r x / deriv (complexSheetProduct s) x

/-- The literal continuous principal-part remainder at an original root. -/
def productPoleRemainder (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : (productSheetCarrier s).subtype) : ℂ → ℂ :=
  simplePoleRemainder (complexSheetProduct s) (complexProductSlabNumerator s r) x

theorem productPoleRemainder_continuousAt (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : (productSheetCarrier s).subtype) : ContinuousAt (productPoleRemainder s r x) (x : ℂ) := by
  have hroot : complexSheetProduct s (x : ℂ) = 0 := by
    rw [complexSheetProduct_ofReal]
    exact x.property
  apply simplePoleRemainder_continuousAt
  · intro z
    exact (complexSheetProduct_hasDerivAt s z).differentiableAt
  · exact complexProductSlabNumerator_differentiable s r (x : ℂ)
  · exact complexSheetProduct_deriv_ne_zero s hroot

theorem complexProductSlabQuotient_principal_part (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : (productSheetCarrier s).subtype) {z : ℂ} (hz : z ≠ (x : ℂ)) :
    complexProductSlabQuotient s r z =
      productPoleResidue s r x / (z - (x : ℂ)) + productPoleRemainder s r x z := by
  exact simplePoleRemainder_identity (complexSheetProduct s) (complexProductSlabNumerator s r)
    (x : ℂ) (by rw [complexSheetProduct_ofReal]; exact x.property) hz

/-- The negative-exponential Fourier jump gives EXACTLY the original physical residue. -/
theorem productPoleResidue_original_mass (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : (productSheetCarrier s).subtype) :
    -((2 * Real.pi : ℝ) * Complex.I) * productPoleResidue s r x = productPhysicalResidue s r x := by
  have hC : (2 * Real.pi : ℝ) * Complex.I ≠ (0 : ℂ) := by
    apply mul_ne_zero
    · exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
    · exact Complex.I_ne_zero
  have hd : deriv (complexSheetProduct s) (x : ℂ) =
      (2 * Real.pi : ℝ) * Complex.I * productSheetTorusDerivative s
        (unitPhase x) (unitPhase (beta * x - 1 / 4)) := by
    rw [(complexSheetProduct_torus_hasDerivAt s (x : ℂ)).deriv,
      complexUnitPhase_ofReal,
      show (beta : ℂ) * (x : ℂ) - 1 / 4 = (beta * x - 1 / 4 : ℝ) by push_cast; ring,
      complexUnitPhase_ofReal]
  have hroot : complexSheetProduct s (x : ℂ) = 0 := by
    rw [complexSheetProduct_ofReal]
    exact x.property
  have hG : productSheetTorusDerivative s (unitPhase x)
      (unitPhase (beta * x - 1 / 4)) ≠ 0 := by
    have h := complexSheetProduct_deriv_ne_zero s hroot
    rw [hd] at h
    exact (mul_ne_zero_iff.mp h).2
  unfold productPoleResidue productPhysicalResidue
  rw [complexProductSlabNumerator_ofReal, hd]
  field_simp

end

end MeyerGeneralProblem.StrongParity
