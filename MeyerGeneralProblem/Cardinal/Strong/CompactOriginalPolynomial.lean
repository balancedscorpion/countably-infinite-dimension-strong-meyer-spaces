module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginalSheetProducts
public import MeyerGeneralProblem.Cardinal.Strong.PolydiskBound
public import MeyerGeneralProblem.Cardinal.Strong.ReciprocalPolynomials

@[expose] public section

/-! The literal original polynomial, derivative, reciprocal identity and compact uniform bounds. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The literal original finite denominator on two independent complex variables. -/
def compactOriginalSheetPolynomial {s : ℕ} (block : CompactOriginalParameterBlock s) (Z W : ℂ) : ℂ :=
  ∏ i : Fin s, sheetPolynomial (block.parameter i) Z W

/-- The actual original torus derivative, with every product-rule term retained. -/
def compactOriginalSheetTorusDerivative {s : ℕ} (block : CompactOriginalParameterBlock s) (Z W : ℂ) : ℂ :=
  ∑ i : Fin s, (∏ j ∈ (Finset.univ : Finset (Fin s)).erase i,
    sheetPolynomial (block.parameter j) Z W) * sheetTorusDerivative (block.parameter i) Z W

/-- The actual compact polynomial equals the entire original product on the quarter flow. -/
theorem compactOriginalSheetPolynomial_onComplexFlow {s : ℕ} (block : CompactOriginalParameterBlock s)
    (z : ℂ) : compactOriginalSheetPolynomial block (complexUnitPhase z)
      (complexUnitPhase (beta * z - 1 / 4)) = compactOriginalComplexSheetProduct block z := rfl

/-- The actual compact entire product has its literal original torus derivative. -/
theorem compactOriginalComplexSheetProduct_torus_hasDerivAt {s : ℕ}
    (block : CompactOriginalParameterBlock s) (z : ℂ) :
    HasDerivAt (compactOriginalComplexSheetProduct block) ((2 * Real.pi : ℝ) * Complex.I *
      compactOriginalSheetTorusDerivative block (complexUnitPhase z)
        (complexUnitPhase (beta * z - 1 / 4))) z := by
  convert! compactOriginalComplexSheetProduct_hasDerivAt block z using 1
  unfold compactOriginalSheetTorusDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [(complexSheetFlow_hasDerivAt (block.parameter i) z).deriv]
  simp only [complexSheetFlow]
  ring

/-- The actual compact original polynomial has constant term one. -/
theorem compactOriginalSheetPolynomial_zero_zero {s : ℕ} (block : CompactOriginalParameterBlock s) :
    compactOriginalSheetPolynomial block 0 0 = 1 := by
  simp [compactOriginalSheetPolynomial, sheetPolynomial]

/-- The explicit nonzero constant for the original finite product polydisk bound. -/
def compactOriginalPolydiskConstant {s : ℕ} (block : CompactOriginalParameterBlock s) : ℝ := ∏ i : Fin s, (1 - block.parameter i)

theorem compactOriginalPolydiskConstant_pos {s : ℕ} (block : CompactOriginalParameterBlock s) : 0 < compactOriginalPolydiskConstant block := by
  apply Finset.prod_pos
  intro i _
  exact sub_pos.mpr (block.parameter_bounds i).2

theorem compactOriginalSheetPolynomial_polydisk_norm_lower {s : ℕ} (block : CompactOriginalParameterBlock s) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) {Z W : ℂ} (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r) :
    compactOriginalPolydiskConstant block * (1 - r) ^ s ≤ ‖compactOriginalSheetPolynomial block Z W‖ := by
  have hp : compactOriginalPolydiskConstant block * (1 - r) ^ s =
      ∏ i : Fin s, (1 - block.parameter i) * (1 - r) := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, compactOriginalPolydiskConstant]
  rw [hp, compactOriginalSheetPolynomial, norm_prod]
  apply Finset.prod_le_prod₀
  · intro i _
    exact mul_nonneg (sub_nonneg.mpr (block.parameter_bounds i).2.le)
      (sub_nonneg.mpr hr1.le)
  · intro i _
    exact sheetPolynomial_polydisk_norm_lower (block.parameter_bounds i).1.le
      (block.parameter_bounds i).2 hr hr1 hZ hW

/-- Literal denominator nonvanishing throughout each closed smaller polydisk. -/
theorem compactOriginalSheetPolynomial_polydisk_ne_zero {s : ℕ} (block : CompactOriginalParameterBlock s) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) {Z W : ℂ} (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r) :
    compactOriginalSheetPolynomial block Z W ≠ 0 := by
  have hpos : 0 < compactOriginalPolydiskConstant block * (1 - r) ^ s :=
    mul_pos (compactOriginalPolydiskConstant_pos block) (pow_pos (sub_pos.mpr hr1) _)
  exact norm_pos_iff.mp (lt_of_lt_of_le hpos
    (compactOriginalSheetPolynomial_polydisk_norm_lower block hr hr1 hZ hW))

/-- The literal compact denominator has the exact original reciprocal sign and degree. -/
theorem compactOriginalSheetPolynomial_reciprocal {s : ℕ} (block : CompactOriginalParameterBlock s) {Z W : ℂ}
    (hZ : Z ≠ 0) (hW : W ≠ 0) :
    (Z * W) ^ s * compactOriginalSheetPolynomial block Z⁻¹ W⁻¹ =
      (-1 : ℂ) ^ s * compactOriginalSheetPolynomial block Z W := by
  calc
    _ = ∏ i : Fin s, (Z * W) * sheetPolynomial (block.parameter i) Z⁻¹ W⁻¹ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, compactOriginalSheetPolynomial, mul_pow]
    _ = ∏ i : Fin s, -sheetPolynomial (block.parameter i) Z W := by
      apply Finset.prod_congr rfl
      intro i _
      exact sheetPolynomial_reciprocal (block.parameter i : ℂ) hZ hW
    _ = ∏ i : Fin s, (-1 : ℂ) * sheetPolynomial (block.parameter i) Z W := by
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, compactOriginalSheetPolynomial]

/-- Compact parameters give a definite dyadic lower bound for the complete product constant. -/
theorem compactOriginalPolydiskConstant_dyadic_lower {s : ℕ} (block : CompactOriginalParameterBlock s) :
    (1 / 2 : ℝ) ^ s ≤ compactOriginalPolydiskConstant block := by
  calc
    _ = ∏ _i : Fin s, (1 / 2 : ℝ) := by simp
    _ ≤ _ := by
      unfold compactOriginalPolydiskConstant
      apply Finset.prod_le_prod₀
      · intro _i _; norm_num
      · intro i _; have h := (block.range i).2; linarith

/-- The reciprocal compact product constant has the definite integer bound 2^s. -/
theorem compactOriginalPolydiskConstant_inv_le {s : ℕ} (block : CompactOriginalParameterBlock s) :
    1 / compactOriginalPolydiskConstant block ≤ (2 : ℝ) ^ s := by
  calc
    _ ≤ 1 / (1 / 2 : ℝ) ^ s :=
      one_div_le_one_div_of_le (by positivity) (compactOriginalPolydiskConstant_dyadic_lower block)
    _ = _ := by rw [one_div_pow]; norm_num

end

end MeyerGeneralProblem.StrongParity
