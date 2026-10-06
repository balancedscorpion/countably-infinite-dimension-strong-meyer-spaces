module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductSeparation

@[expose] public section

/-! Original ProductSeparation for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The original finite parameter-gap factor, which is strictly positive. -/
def productSheetParameterGap {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) : ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin s)).erase i,
    |block.parameter j - block.parameter i|

theorem productSheetParameterGap_pos {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) :
    0 < productSheetParameterGap block i := by
  apply Finset.prod_pos
  intro j hj
  apply abs_pos.mpr
  exact sub_ne_zero.mpr ((block.injective).ne (Finset.mem_erase.mp hj).1)

/-- The exact derivative factorization at any selected original sheet root. -/
theorem productSheetTorusDerivative_at_root {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) {Z W : ℂ}
    (hroot : sheetPolynomial (block.parameter i) Z W = 0) :
    compactOriginalSheetTorusDerivative block Z W =
      (∏ j ∈ (Finset.univ : Finset (Fin s)).erase i,
        ((block.parameter j : ℂ) - (block.parameter i : ℂ))) *
          (Z - W) ^ (s - 1) * sheetTorusDerivative (block.parameter i) Z W := by
  unfold compactOriginalSheetTorusDerivative
  rw [Finset.sum_eq_single i]
  · simp only [sheetPolynomial_at_other_root hroot, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  · intro j _ hji
    have hprod : (∏ k ∈ (Finset.univ : Finset (Fin s)).erase j,
        sheetPolynomial (block.parameter k) Z W) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩) hroot
    rw [hprod, zero_mul]
  · simp

/-- The literal factorization also retains every absolute parameter gap. -/
theorem productSheetTorusDerivative_norm_at_root {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) {Z W : ℂ}
    (hroot : sheetPolynomial (block.parameter i) Z W = 0) :
    ‖compactOriginalSheetTorusDerivative block Z W‖ = productSheetParameterGap block i *
      ‖Z - W‖ ^ (s - 1) * ‖sheetTorusDerivative (block.parameter i) Z W‖ := by
  rw [productSheetTorusDerivative_at_root block i hroot, norm_mul, norm_mul, norm_pow,
    norm_prod]
  congr 2
  apply Finset.prod_congr rfl
  intro j _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- A finite, explicit residue-growth constant for each original sheet. -/
def productSheetResidueConstant {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) : ℝ :=
  sheetPhaseSeparationConstant ^ (s - 1) /
    (productSheetParameterGap block i * (1 - block.parameter i))

theorem productSheetResidueConstant_pos {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) :
    0 < productSheetResidueConstant block i := by
  dsimp [productSheetResidueConstant]
  exact div_pos (pow_pos sheetPhaseSeparationConstant_pos _)
    (mul_pos (productSheetParameterGap_pos block i)
      (sub_pos.mpr (block.parameter_bounds i).2))

/-- The reciprocal original product denominator grows at most polynomially
on every actual root of a selected sheet. -/
theorem productSheetTorusDerivative_inverse_norm_upper {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) (x : ℝ)
    (hroot : sheetFlow (block.parameter i) x = 0) :
    1 / ‖compactOriginalSheetTorusDerivative block (unitPhase x)
      (unitPhase (beta * x - 1 / 4))‖ ≤
      productSheetResidueConstant block i * (1 + |x|) ^ (s - 1) := by
  let a := block.parameter i
  let q := ‖unitPhase x - unitPhase (beta * x - 1 / 4)‖
  let D := ‖sheetTorusDerivative a (unitPhase x) (unitPhase (beta * x - 1 / 4))‖
  have ha : 0 ≤ a := (block.parameter_bounds i).1.le
  have ha1 : a < 1 := (block.parameter_bounds i).2
  have hr : sheetPolynomial a (unitPhase x) (unitPhase (beta * x - 1 / 4)) = 0 := hroot
  have hsep := quarterFlow_sheet_separation
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] using ha1.le) x hr
  have hsep' : 1 / (sheetPhaseSeparationConstant * (1 + |x|)) ≤ q := hsep
  have hden : 0 < sheetPhaseSeparationConstant * (1 + |x|) := by
    exact mul_pos sheetPhaseSeparationConstant_pos (by positivity)
  have hqpos : 0 < q := lt_of_lt_of_le (one_div_pos.mpr hden) hsep'
  have hD : 1 - a ≤ D := sheetTorusDerivative_norm_lower ha ha1 (unitPhase_norm _) hr
  have hDpos : 0 < D := lt_of_lt_of_le (sub_pos.mpr ha1) hD
  have hgap := productSheetParameterGap_pos block i
  have hqinv : 1 / q ≤ sheetPhaseSeparationConstant * (1 + |x|) := by
    have := one_div_le_one_div_of_le (by positivity) hsep'
    simpa only [one_div_one_div] using this
  rw [productSheetTorusDerivative_norm_at_root block i hr]
  change 1 / (productSheetParameterGap block i * q ^ (s - 1) * D) ≤ _
  calc
    _ = (1 / productSheetParameterGap block i) * (1 / q) ^ (s - 1) * (1 / D) := by
      rw [div_pow]
      field_simp
      simp
    _ ≤ (1 / productSheetParameterGap block i) *
        (sheetPhaseSeparationConstant * (1 + |x|)) ^ (s - 1) * (1 / (1 - a)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hqinv _)
          (by positivity)
      · exact one_div_le_one_div_of_le (sub_pos.mpr ha1) hD
      · positivity
      · exact mul_nonneg (by positivity) (pow_nonneg hden.le _)
    _ = _ := by
      dsimp [productSheetResidueConstant, a]
      rw [mul_pow]
      field_simp

/-- The physical residue formula with a bounded numerator has the actual
growth order `s-1` on the complete selected sheet. -/
theorem productSheetResidue_norm_upper {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) (x : ℝ)
    (hroot : sheetFlow (block.parameter i) x = 0) (R : ℂ) (B : ℝ)
    (hR : ‖R‖ ≤ B) :
    ‖-R / compactOriginalSheetTorusDerivative block (unitPhase x)
      (unitPhase (beta * x - 1 / 4))‖ ≤
      B * productSheetResidueConstant block i * (1 + |x|) ^ (s - 1) := by
  rw [norm_div, norm_neg]
  calc
    _ = ‖R‖ * (1 / ‖compactOriginalSheetTorusDerivative block (unitPhase x)
        (unitPhase (beta * x - 1 / 4))‖) := by ring
    _ ≤ B * (productSheetResidueConstant block i * (1 + |x|) ^ (s - 1)) :=
      mul_le_mul hR (productSheetTorusDerivative_inverse_norm_upper block i x hroot)
        (by positivity) ((norm_nonneg R).trans hR)
    _ = _ := by ring

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
