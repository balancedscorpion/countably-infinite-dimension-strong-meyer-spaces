module

public import MeyerGeneralProblem.Cardinal.Strong.SheetProducts

@[expose] public section

/-!
# Original finite-product derivative denominator

At a selected sheet root every other sheet equals its parameter
difference times the literal phase difference. The complete product
derivative therefore has the exact original confluent factorization.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The original finite polynomial product in the two torus variables. -/
def productSheetPolynomial (s : ℕ) (Z W : ℂ) : ℂ :=
  ∏ i : Fin s, sheetPolynomial (productSheetParameter s i) Z W

/-- `D_beta P_s`, computed by the product rule on the literal factors. -/
def productSheetTorusDerivative (s : ℕ) (Z W : ℂ) : ℂ :=
  ∑ i : Fin s, (∏ j ∈ (Finset.univ : Finset (Fin s)).erase i,
    sheetPolynomial (productSheetParameter s j) Z W) *
      sheetTorusDerivative (productSheetParameter s i) Z W

/-- The original finite parameter-gap factor, which is strictly positive. -/
def productSheetParameterGap (s : ℕ) (i : Fin s) : ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin s)).erase i,
    |productSheetParameter s j - productSheetParameter s i|

theorem productSheetParameterGap_pos (s : ℕ) (i : Fin s) :
    0 < productSheetParameterGap s i := by
  apply Finset.prod_pos
  intro j hj
  apply abs_pos.mpr
  exact sub_ne_zero.mpr ((productSheetParameter_injective s).ne (Finset.mem_erase.mp hj).1)

theorem sheetPolynomial_at_other_root {a b Z W : ℂ} (hroot : sheetPolynomial a Z W = 0) :
    sheetPolynomial b Z W = (b - a) * (Z - W) := by
  rw [← sheetPolynomial_parameter_difference, hroot, sub_zero]

/-- The exact derivative factorization at any selected original sheet root. -/
theorem productSheetTorusDerivative_at_root (s : ℕ) (i : Fin s) {Z W : ℂ}
    (hroot : sheetPolynomial (productSheetParameter s i) Z W = 0) :
    productSheetTorusDerivative s Z W =
      (∏ j ∈ (Finset.univ : Finset (Fin s)).erase i,
        ((productSheetParameter s j : ℂ) - (productSheetParameter s i : ℂ))) *
          (Z - W) ^ (s - 1) * sheetTorusDerivative (productSheetParameter s i) Z W := by
  unfold productSheetTorusDerivative
  rw [Finset.sum_eq_single i]
  · simp only [sheetPolynomial_at_other_root hroot, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  · intro j _ hji
    have hprod : (∏ k ∈ (Finset.univ : Finset (Fin s)).erase j,
        sheetPolynomial (productSheetParameter s k) Z W) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩) hroot
    rw [hprod, zero_mul]
  · simp

/-- The literal factorization also retains every absolute parameter gap. -/
theorem productSheetTorusDerivative_norm_at_root (s : ℕ) (i : Fin s) {Z W : ℂ}
    (hroot : sheetPolynomial (productSheetParameter s i) Z W = 0) :
    ‖productSheetTorusDerivative s Z W‖ = productSheetParameterGap s i *
      ‖Z - W‖ ^ (s - 1) * ‖sheetTorusDerivative (productSheetParameter s i) Z W‖ := by
  rw [productSheetTorusDerivative_at_root s i hroot, norm_mul, norm_mul, norm_pow,
    norm_prod]
  congr 2
  apply Finset.prod_congr rfl
  intro j _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The numerical constant in the proved parity phase separation. -/
def sheetPhaseSeparationConstant : ℝ := 8 * (3 * beta + 2)

theorem sheetPhaseSeparationConstant_pos : 0 < sheetPhaseSeparationConstant := by
  dsimp [sheetPhaseSeparationConstant]
  obtain ⟨hbeta, _⟩ := beta_between_three_four
  linarith

/-- A finite, explicit residue-growth constant for each original sheet. -/
def productSheetResidueConstant (s : ℕ) (i : Fin s) : ℝ :=
  sheetPhaseSeparationConstant ^ (s - 1) /
    (productSheetParameterGap s i * (1 - productSheetParameter s i))

theorem productSheetResidueConstant_pos (s : ℕ) (i : Fin s) :
    0 < productSheetResidueConstant s i := by
  dsimp [productSheetResidueConstant]
  exact div_pos (pow_pos sheetPhaseSeparationConstant_pos _)
    (mul_pos (productSheetParameterGap_pos s i)
      (sub_pos.mpr (productSheetParameter_bounds s i).2))

/-- The reciprocal original product denominator grows at most polynomially
on every actual root of a selected sheet. -/
theorem productSheetTorusDerivative_inverse_norm_upper (s : ℕ) (i : Fin s) (x : ℝ)
    (hroot : sheetFlow (productSheetParameter s i) x = 0) :
    1 / ‖productSheetTorusDerivative s (unitPhase x)
      (unitPhase (beta * x - 1 / 4))‖ ≤
      productSheetResidueConstant s i * (1 + |x|) ^ (s - 1) := by
  let a := productSheetParameter s i
  let q := ‖unitPhase x - unitPhase (beta * x - 1 / 4)‖
  let D := ‖sheetTorusDerivative a (unitPhase x) (unitPhase (beta * x - 1 / 4))‖
  have ha : 0 ≤ a := (productSheetParameter_bounds s i).1.le
  have ha1 : a < 1 := (productSheetParameter_bounds s i).2
  have hr : sheetPolynomial a (unitPhase x) (unitPhase (beta * x - 1 / 4)) = 0 := hroot
  have hsep := quarterFlow_sheet_separation
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] using ha1.le) x hr
  have hsep' : 1 / (sheetPhaseSeparationConstant * (1 + |x|)) ≤ q := hsep
  have hden : 0 < sheetPhaseSeparationConstant * (1 + |x|) := by
    exact mul_pos sheetPhaseSeparationConstant_pos (by positivity)
  have hqpos : 0 < q := lt_of_lt_of_le (one_div_pos.mpr hden) hsep'
  have hD : 1 - a ≤ D := sheetTorusDerivative_norm_lower ha ha1 (unitPhase_norm _) hr
  have hDpos : 0 < D := lt_of_lt_of_le (sub_pos.mpr ha1) hD
  have hgap := productSheetParameterGap_pos s i
  have hqinv : 1 / q ≤ sheetPhaseSeparationConstant * (1 + |x|) := by
    have := one_div_le_one_div_of_le (by positivity) hsep'
    simpa only [one_div_one_div] using this
  rw [productSheetTorusDerivative_norm_at_root s i hr]
  change 1 / (productSheetParameterGap s i * q ^ (s - 1) * D) ≤ _
  calc
    _ = (1 / productSheetParameterGap s i) * (1 / q) ^ (s - 1) * (1 / D) := by
      rw [div_pow]
      field_simp
      simp
    _ ≤ (1 / productSheetParameterGap s i) *
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
theorem productSheetResidue_norm_upper (s : ℕ) (i : Fin s) (x : ℝ)
    (hroot : sheetFlow (productSheetParameter s i) x = 0) (R : ℂ) (B : ℝ)
    (hR : ‖R‖ ≤ B) :
    ‖-R / productSheetTorusDerivative s (unitPhase x)
      (unitPhase (beta * x - 1 / 4))‖ ≤
      B * productSheetResidueConstant s i * (1 + |x|) ^ (s - 1) := by
  rw [norm_div, norm_neg]
  calc
    _ = ‖R‖ * (1 / ‖productSheetTorusDerivative s (unitPhase x)
        (unitPhase (beta * x - 1 / 4))‖) := by ring
    _ ≤ B * (productSheetResidueConstant s i * (1 + |x|) ^ (s - 1)) :=
      mul_le_mul hR (productSheetTorusDerivative_inverse_norm_upper s i x hroot)
        (by positivity) ((norm_nonneg R).trans hR)
    _ = _ := by ring

end

end MeyerGeneralProblem.StrongParity
