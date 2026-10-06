module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginalPolynomial
public import MeyerGeneralProblem.Cardinal.Strong.ProductPowerSeries

@[expose] public section

/-! Complete literal compact original reciprocal coefficients in the first variable. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The literal multi-index geometric series represents the original finite reciprocal. -/
theorem compactOriginalProductSheetReciprocal_multi_hasSum {s : ℕ} (block : CompactOriginalParameterBlock s) {Z W : ℂ}
    (hZ : ‖Z‖ < 1) (hW : ‖W‖ ≤ 1) :
    HasSum (fun v : Fin s → ℕ =>
      ∏ i : Fin s, sheetZCoefficient (block.parameter i) (v i) W * Z ^ (v i))
      (compactOriginalSheetPolynomial block Z W)⁻¹ := by
  have h := hasSum_finiteSeriesProduct s
    (fun i k => sheetZCoefficient (block.parameter i) k W * Z ^ k)
    (fun i => (sheetPolynomial (block.parameter i) Z W)⁻¹)
    (fun i => sheetZCoefficient_hasSum (block.parameter_bounds i).1.le
      (block.parameter_bounds i).2 hW hZ)
  simpa only [Finset.prod_inv_distrib, compactOriginalSheetPolynomial] using h

/-- The literal finite product coefficient, retaining every degree composition. -/
def compactOriginalZCoefficient {s : ℕ} (block : CompactOriginalParameterBlock s) (k : ℕ) (W : ℂ) : ℂ :=
  ∑ v ∈ productZCompositions s k,
    ∏ i : Fin s, sheetZCoefficient (block.parameter i) (v i) W

theorem compactOriginalZCoefficient_term_norm_le {s : ℕ} (block : CompactOriginalParameterBlock s) (k : ℕ) (v : Fin s → Fin (k + 1))
    {W : ℂ} (hW : ‖W‖ ≤ 1) :
    ‖∏ i : Fin s, sheetZCoefficient (block.parameter i) (v i) W‖ ≤
      1 / compactOriginalPolydiskConstant block := by
  rw [norm_prod]
  calc
    _ ≤ ∏ i : Fin s, 1 / (1 - block.parameter i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact norm_nonneg _
      · intro i _
        exact sheetZCoefficient_norm_le (block.parameter_bounds i).1.le
          (block.parameter_bounds i).2 _ hW
    _ = _ := by simp only [one_div, Finset.prod_inv_distrib, compactOriginalPolydiskConstant]

/-- The actual coefficient is polynomially bounded uniformly on the closed W disk. -/
theorem compactOriginalZCoefficient_norm_le {s : ℕ} (block : CompactOriginalParameterBlock s) (k : ℕ) {W : ℂ} (hW : ‖W‖ ≤ 1) :
    ‖compactOriginalZCoefficient block k W‖ ≤ (k + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block := by
  have hC := compactOriginalPolydiskConstant_pos block
  have hcard : ((productZCompositions s k).card : ℝ) ≤ (k + 1 : ℝ) ^ s := by
    exact_mod_cast productZCompositions_card_le s k
  calc
    _ ≤ ∑ v ∈ productZCompositions s k,
        ‖∏ i : Fin s, sheetZCoefficient (block.parameter i) (v i) W‖ := by
      unfold compactOriginalZCoefficient
      exact norm_sum_le _ _
    _ ≤ ∑ _v ∈ productZCompositions s k, 1 / compactOriginalPolydiskConstant block := by
      exact Finset.sum_le_sum (fun v _ => compactOriginalZCoefficient_term_norm_le block k v hW)
    _ = ((productZCompositions s k).card : ℝ) * (1 / compactOriginalPolydiskConstant block) := by simp
    _ ≤ (k + 1 : ℝ) ^ s * (1 / compactOriginalPolydiskConstant block) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem compactOriginalZCoefficient_differentiableOn {s : ℕ} (block : CompactOriginalParameterBlock s) (k : ℕ) :
    DifferentiableOn ℂ (compactOriginalZCoefficient block k) (Metric.closedBall 0 1) := by
  unfold compactOriginalZCoefficient
  apply DifferentiableOn.fun_sum
  intro v _
  apply DifferentiableOn.fun_finsetProd
  intro i _
  exact sheetZCoefficient_differentiableOn (block.parameter_bounds i).1.le
    (block.parameter_bounds i).2 _

/-- The actual original product reciprocal has exactly the literal finite Z coefficients. -/
theorem compactOriginalZCoefficient_hasSum {s : ℕ} (block : CompactOriginalParameterBlock s) {Z W : ℂ}
    (hZ : ‖Z‖ < 1) (hW : ‖W‖ ≤ 1) :
    HasSum (fun k : ℕ => compactOriginalZCoefficient block k W * Z ^ k)
      (compactOriginalSheetPolynomial block Z W)⁻¹ := by
  let F : (Fin s → ℕ) → ℂ := fun v =>
    ∏ i : Fin s, sheetZCoefficient (block.parameter i) (v i) W * Z ^ (v i)
  have hmulti : HasSum F (compactOriginalSheetPolynomial block Z W)⁻¹ :=
    compactOriginalProductSheetReciprocal_multi_hasSum block hZ hW
  have hfiber (k : ℕ) :
      (∑' v : {v : Fin s → ℕ // ∑ i : Fin s, v i = k}, F v.val) =
        compactOriginalZCoefficient block k W * Z ^ k := by
    rw [← (productZDegreeFiberEquiv s k).symm.tsum_eq
      (fun v : {v : Fin s → ℕ // ∑ i : Fin s, v i = k} => F v.val), tsum_fintype]
    calc
      _ = ∑ v : (productZCompositions s k),
          (∏ i : Fin s, sheetZCoefficient (block.parameter i) (v.val i) W) * Z ^ k := by
        apply Finset.sum_congr rfl
        intro v _
        change (∏ i : Fin s,
          sheetZCoefficient (block.parameter i) (v.val i) W * Z ^ (v.val i : ℕ)) = _
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        have hdegree : ∑ i : Fin s, (v.val i : ℕ) = k := (Finset.mem_filter.mp v.property).2
        rw [hdegree]
      _ = _ := by
        rw [← Finset.sum_mul]
        exact congrArg (fun u : ℂ => u * Z ^ k)
          (Finset.sum_coe_sort (productZCompositions s k)
            (fun v : Fin s → Fin (k + 1) =>
              ∏ i : Fin s, sheetZCoefficient (block.parameter i) (v i) W))
  have hgroup := hmulti.tsum_fiberwise (fun v : Fin s → ℕ => ∑ i : Fin s, v i)
  exact hgroup.congr_fun (fun k => (hfiber k).symm)

end

end MeyerGeneralProblem.StrongParity
