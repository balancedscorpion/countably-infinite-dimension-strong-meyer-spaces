module

public import MeyerGeneralProblem.Cardinal.Strong.ProductAnnihilator
public import MeyerGeneralProblem.Cardinal.Strong.OriginalStrongClearingRecurrence

@[expose] public section

/-! Actual positive native polynomials for complete original sheet products.
The original quarter phase is retained in both W coefficients. Finite motifs
are the actual coefficient support, so no polynomial representation certificate
is an input to the scheduled-prefix clearing theorem. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Actual positive native frequency homomorphism. -/
def originalPositiveFrequencyHom : (ℕ × ℕ) →+ ℝ where
  toFun := positiveConeFrequency
  map_zero' := by simp [positiveConeFrequency]
  map_add' a b := by simp only [positiveConeFrequency, Prod.fst_add, Prod.snd_add, Nat.cast_add]; ring

/-- Actual entire characters at an ordinary common scale. -/
def originalPositiveEntireCharacter (scale : ℝ) (z : ℂ) : Multiplicative (ℕ × ℕ) →* ℂ where
  toFun n := complexUnitPhase (((originalPositiveFrequencyHom n.toAdd / scale : ℝ) : ℂ) * z)
  map_one' := by simp [complexUnitPhase]
  map_mul' a b := by
    change complexUnitPhase (((originalPositiveFrequencyHom (a.toAdd + b.toAdd) / scale : ℝ) : ℂ) * z) = _
    simp only [map_add, add_div, Complex.ofReal_add, add_mul, complexUnitPhase, mul_add, Complex.exp_add]

/-- Exact value of the actual positive entire character. -/
theorem originalPositiveEntireCharacter_apply (scale : ℝ) (z : ℂ) (p : ℕ × ℕ) :
    originalPositiveEntireCharacter scale z (Multiplicative.ofAdd p) =
      complexUnitPhase (((positiveConeFrequency p / scale : ℝ) : ℂ) * z) := rfl

/-- Genuine algebra evaluation, respecting every coefficient collision. -/
def originalPositivePolynomialEvaluation (scale : ℝ) (z : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℕ) →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (ℕ × ℕ) (originalPositiveEntireCharacter scale z)

/-- The literal sheet after a positive integer coordinate dilation. -/
def originalPositiveSheetPolynomial (d : ℕ) (a : ℝ) : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  AddMonoidAlgebra.single (0, 0) 1 -
    AddMonoidAlgebra.single (0, d) ((a : ℂ) * complexUnitPhase (-1 / 4)) +
    AddMonoidAlgebra.single (d, 0) (a : ℂ) -
    AddMonoidAlgebra.single (d, d) (complexUnitPhase (-1 / 4))

/-- Exact original entire sheet evaluation, with its unaltered quarter phase. -/
theorem originalPositivePolynomialEvaluation_sheet (scale : ℝ) (d : ℕ) (a : ℝ) (z : ℂ) :
    originalPositivePolynomialEvaluation scale z (originalPositiveSheetPolynomial d a) =
      complexSheetFlow a (((d : ℝ) / scale : ℝ) * z) := by
  let u : ℂ := (((d : ℝ) / scale : ℝ) : ℂ) * z
  have hw : complexUnitPhase (-1 / 4) * complexUnitPhase (beta * u) =
      complexUnitPhase (beta * u - 1 / 4) := by
    unfold complexUnitPhase
    rw [← Complex.exp_add]
    congr 1
    ring
  have hzw : complexUnitPhase ((((d : ℝ) + beta * d) / scale : ℝ) * z) =
      complexUnitPhase u * complexUnitPhase (beta * u) := by
    unfold complexUnitPhase
    rw [← Complex.exp_add]
    congr 1
    dsimp [u]
    push_cast
    ring
  simp only [originalPositiveSheetPolynomial, map_sub, map_add,
    originalPositivePolynomialEvaluation, AddMonoidAlgebra.lift_single, smul_eq_mul]
  simp only [originalPositiveEntireCharacter_apply, positiveConeFrequency,
    Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add, zero_div,
    Complex.ofReal_zero, one_mul]
  change complexUnitPhase 0 - (a : ℂ) * complexUnitPhase (-1 / 4) *
      complexUnitPhase (((beta * d / scale : ℝ) : ℂ) * z) +
      (a : ℂ) * complexUnitPhase (((d / scale : ℝ) : ℂ) * z) -
      complexUnitPhase (-1 / 4) * complexUnitPhase ((((d : ℝ) + beta * d) / scale : ℝ) * z) = _
  rw [hzw, show complexUnitPhase 0 = 1 by simp [complexUnitPhase]]
  have hbu : (((beta * d / scale : ℝ) : ℂ) * z) = beta * u := by dsimp [u]; push_cast; ring
  rw [hbu]
  change 1 - (a : ℂ) * complexUnitPhase (-1 / 4) * complexUnitPhase (beta * u) +
      (a : ℂ) * complexUnitPhase u -
      complexUnitPhase (-1 / 4) * (complexUnitPhase u * complexUnitPhase (beta * u)) = complexSheetFlow a u
  unfold complexSheetFlow sheetPolynomial
  rw [← hw]
  ring

/-- Every actual real evaluation character is the original modulation character. -/
theorem originalPositiveEntireCharacter_ofReal (scale : ℝ) (x : ℝ) (p : ℕ × ℕ) :
    originalPositiveEntireCharacter scale x (Multiplicative.ofAdd p) =
      combModulationCharacter (positiveConeFrequency p / scale) x := by
  rw [originalPositiveEntireCharacter_apply, combModulationCharacter_eq_exp]
  unfold complexUnitPhase
  congr 1
  push_cast
  ring

/-- The complete finite motif is the ACTUAL nonzero coefficient support. -/
abbrev OriginalPositivePolynomialMotif (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) := ↥q.coeff.support

/-- Actual positive coordinates of every nonzero motif. -/
def originalPositivePolynomialCoordinates (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    OriginalPositivePolynomialMotif q → ℕ × ℕ := Subtype.val

/-- The genuine coefficient, after all polynomial collisions have been summed. -/
def originalPositivePolynomialCoefficient (q : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (p : OriginalPositivePolynomialMotif q) : ℂ := q.coeff p.val

/-- Exact finite positive-frequency representation of EVERY actual polynomial. -/
theorem originalPositivePolynomialEvaluation_finiteSymbol (scale x : ℝ)
    (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    finitePositiveExponentialSymbol
      (originalPositivePolynomialFrequency scale (originalPositivePolynomialCoordinates q))
      (originalPositivePolynomialCoefficient q) x = originalPositivePolynomialEvaluation scale x q := by
  classical
  rw [originalPositivePolynomialEvaluation, AddMonoidAlgebra.lift_apply']
  simp only [Algebra.algebraMap_self, RingHom.id_apply, originalPositiveEntireCharacter_ofReal,
    Finsupp.sum, finitePositiveExponentialSymbol, originalPositivePolynomialFrequency,
    originalPositivePolynomialCoordinates, originalPositivePolynomialCoefficient]
  exact Finset.sum_attach q.coeff.support (fun p => q.coeff p * combModulationCharacter (positiveConeFrequency p / scale) x)

end
end MeyerGeneralProblem.StrongParity
