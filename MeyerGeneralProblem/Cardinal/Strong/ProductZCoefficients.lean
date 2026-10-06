module

public import MeyerGeneralProblem.Cardinal.Strong.SheetPowerSeries

@[expose] public section

/-! Actual finite composition coefficients of the original product in Z.
The complete finite composition set has a direct polynomial cardinal
bound. Holomorphy and norm bounds are discharged on the literal sum. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- All original degree-k compositions, inside the complete finite box. -/
def productZCompositions (s k : ℕ) : Finset (Fin s → Fin (k + 1)) :=
  Finset.univ.filter (fun v => ∑ i : Fin s, (v i : ℕ) = k)

/-- The literal finite product coefficient, retaining every degree composition. -/
def productZCoefficient (s k : ℕ) (W : ℂ) : ℂ :=
  ∑ v ∈ productZCompositions s k,
    ∏ i : Fin s, sheetZCoefficient (productSheetParameter s i) (v i) W

theorem productZCompositions_card_le (s k : ℕ) :
    (productZCompositions s k).card ≤ (k + 1) ^ s := by
  have h := Finset.card_le_card
    (Finset.filter_subset (fun v : Fin s → Fin (k + 1) => ∑ i, (v i : ℕ) = k) Finset.univ)
  simpa only [productZCompositions, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin] using h

theorem productZCoefficient_term_norm_le (s k : ℕ) (v : Fin s → Fin (k + 1))
    {W : ℂ} (hW : ‖W‖ ≤ 1) :
    ‖∏ i : Fin s, sheetZCoefficient (productSheetParameter s i) (v i) W‖ ≤
      1 / productPolydiskConstant s := by
  rw [norm_prod]
  calc
    _ ≤ ∏ i : Fin s, 1 / (1 - productSheetParameter s i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact norm_nonneg _
      · intro i _
        exact sheetZCoefficient_norm_le (productSheetParameter_bounds s i).1.le
          (productSheetParameter_bounds s i).2 _ hW
    _ = _ := by simp only [one_div, Finset.prod_inv_distrib, productPolydiskConstant]

/-- The actual coefficient is polynomially bounded uniformly on the closed W disk. -/
theorem productZCoefficient_norm_le (s k : ℕ) {W : ℂ} (hW : ‖W‖ ≤ 1) :
    ‖productZCoefficient s k W‖ ≤ (k + 1 : ℝ) ^ s / productPolydiskConstant s := by
  have hC := productPolydiskConstant_pos s
  have hcard : ((productZCompositions s k).card : ℝ) ≤ (k + 1 : ℝ) ^ s := by
    exact_mod_cast productZCompositions_card_le s k
  calc
    _ ≤ ∑ v ∈ productZCompositions s k,
        ‖∏ i : Fin s, sheetZCoefficient (productSheetParameter s i) (v i) W‖ := by
      unfold productZCoefficient
      exact norm_sum_le _ _
    _ ≤ ∑ _v ∈ productZCompositions s k, 1 / productPolydiskConstant s := by
      exact Finset.sum_le_sum (fun v _ => productZCoefficient_term_norm_le s k v hW)
    _ = ((productZCompositions s k).card : ℝ) * (1 / productPolydiskConstant s) := by simp
    _ ≤ (k + 1 : ℝ) ^ s * (1 / productPolydiskConstant s) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem productZCoefficient_differentiableOn (s k : ℕ) :
    DifferentiableOn ℂ (productZCoefficient s k) (Metric.closedBall 0 1) := by
  unfold productZCoefficient
  apply DifferentiableOn.fun_sum
  intro v _
  apply DifferentiableOn.fun_finsetProd
  intro i _
  exact sheetZCoefficient_differentiableOn (productSheetParameter_bounds s i).1.le
    (productSheetParameter_bounds s i).2 _

end

end MeyerGeneralProblem.StrongParity
