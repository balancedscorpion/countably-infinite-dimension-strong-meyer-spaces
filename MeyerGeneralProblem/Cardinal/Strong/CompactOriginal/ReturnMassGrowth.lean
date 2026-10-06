module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.PhysicalDistribution
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductResidues
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductSeparation
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ReturnCorner
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ReturnMassGrowth

@[expose] public section

/-! Complete original ReturnMassGrowth for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open Filter
open scoped Topology

/-- The explicit upper denominator constant at the original sheet returns. -/
def productReturnDenominatorConstant {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) : ℝ :=
  productSheetParameterGap block i * (2 * Real.pi * beta) ^ (s - 1) *
    ((1 + beta) * (1 + block.parameter i))

theorem productReturnDenominatorConstant_pos {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) :
    0 < productReturnDenominatorConstant block i := by
  have hb : 0 < beta := by linarith [beta_between_three_four.1]
  have ha := (block.parameter_bounds i).1
  have hgap := productSheetParameterGap_pos block i
  dsimp [productReturnDenominatorConstant]
  positivity

theorem productPrivateReturn_derivative_norm_pos {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) (n : ℕ) :
    0 < ‖compactOriginalSheetTorusDerivative block (unitPhase (privateProductSheetRoot block i n))
      (unitPhase (beta * privateProductSheetRoot block i n - 1 / 4))‖ := by
  let x : ℝ := privateProductSheetRoot block i n
  let a := block.parameter i
  have ha : 0 ≤ a := (block.parameter_bounds i).1.le
  have ha1 : a < 1 := (block.parameter_bounds i).2
  have hr : sheetPolynomial a (unitPhase x) (unitPhase (beta * x - 1 / 4)) = 0 :=
    privateSheetRoot_is_root a ha n
  have hb : 0 < beta := by linarith [beta_between_three_four.1]
  have haC : ‖(a : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] using ha1.le
  have hsep := quarterFlow_sheet_separation haC x hr
  have hq : 0 < ‖unitPhase x - unitPhase (beta * x - 1 / 4)‖ :=
    lt_of_lt_of_le (by positivity) hsep
  have hD : 0 < ‖sheetTorusDerivative a (unitPhase x) (unitPhase (beta * x - 1 / 4))‖ :=
    lt_of_lt_of_le (sub_pos.mpr ha1)
      (sheetTorusDerivative_norm_lower ha ha1 (unitPhase_norm _) hr)
  rw [productSheetTorusDerivative_norm_at_root block i hr]
  exact mul_pos (mul_pos (productSheetParameterGap_pos block i) (pow_pos hq _)) hD

/-- The actual product denominator is at most a constant times the inverse
return denominator to power `s-1`. -/
theorem productPrivateReturn_derivative_norm_upper {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) (n : ℕ) :
    ‖compactOriginalSheetTorusDerivative block (unitPhase (privateProductSheetRoot block i n))
      (unitPhase (beta * privateProductSheetRoot block i n - 1 / 4))‖ ≤
      productReturnDenominatorConstant block i / |(quarterN (n + 5) : ℝ)| ^ (s - 1) := by
  let x : ℝ := privateProductSheetRoot block i n
  let a := block.parameter i
  let B := |(quarterN (n + 5) : ℝ)|
  let K := 2 * Real.pi * beta
  let U := (1 + beta) * (1 + a)
  have ha : 0 ≤ a := (block.parameter_bounds i).1.le
  have hr : sheetPolynomial a (unitPhase x) (unitPhase (beta * x - 1 / 4)) = 0 :=
    privateSheetRoot_is_root a ha n
  have hb : 0 < beta := by linarith [beta_between_three_four.1]
  have hK : 0 < K := by dsimp [K]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hgap := productSheetParameterGap_pos block i
  have hB : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (privateReturn_denominator_lower n)
  have hq : ‖unitPhase x - unitPhase (beta * x - 1 / 4)‖ ≤ K / B := by
    have h := (privateSheetRoot_phase_bounds a ha n).2.2
    exact h.trans ((mul_le_mul_of_nonneg_left (privateReturnError_abs_le n) hK.le).trans_eq
      (by dsimp [K, B]; ring))
  have hD : ‖sheetTorusDerivative a (unitPhase x) (unitPhase (beta * x - 1 / 4))‖ ≤ U :=
    sheetTorusDerivative_norm_upper ha (unitPhase_norm _) (unitPhase_norm _)
  rw [productSheetTorusDerivative_norm_at_root block i hr]
  calc
    _ ≤ productSheetParameterGap block i * (K / B) ^ (s - 1) * U := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq _) hgap.le
      · exact hD
      · exact norm_nonneg _
      · positivity
    _ = _ := by
      dsimp [productReturnDenominatorConstant, K, U, a, B]
      rw [div_pow]
      ring

theorem privateProductSheetRoot_weight_upper {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) (n : ℕ) (N : ℕ) :
    (1 + |(privateProductSheetRoot block i n : ℝ)|) ^ N ≤
      2 ^ N * |(quarterN (n + 5) : ℝ)| ^ N := by
  have hdist := (privateSheetRoot_distance (block.parameter i)
    (block.parameter_bounds i).1.le n).trans (privateReturnError_small n)
  change |(privateProductSheetRoot block i n : ℝ) - (quarterN (n + 5) : ℝ)| ≤ 1 / 6 at hdist
  have ht' : |(privateProductSheetRoot block i n : ℝ)| ≤
      |(quarterN (n + 5) : ℝ)| +
        |(privateProductSheetRoot block i n : ℝ) - (quarterN (n + 5) : ℝ)| := by
    have h := abs_add_le (quarterN (n + 5) : ℝ)
      ((privateProductSheetRoot block i n : ℝ) - (quarterN (n + 5) : ℝ))
    rw [show (quarterN (n + 5) : ℝ) +
      ((privateProductSheetRoot block i n : ℝ) - (quarterN (n + 5) : ℝ)) =
        (privateProductSheetRoot block i n : ℝ) by ring] at h
    exact h
  have hB := privateReturn_denominator_lower n
  have hbound : 1 + |(privateProductSheetRoot block i n : ℝ)| ≤
      2 * |(quarterN (n + 5) : ℝ)| := by linarith
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hbound N

/-- A nonzero original corner value forces a positive lower weighted
summand along the ACTUAL escaping roots at every low exponent. -/
theorem productPhysicalResidue_privateReturn_eventually_lower
    {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) (r : productNumeratorIndex s → ℂ)
    (hJ : productSlabCornerValue s r ≠ 0) (N : ℕ) (hN : N ≤ s - 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      c ≤ ‖productPhysicalResidue block r (privateProductSheetRoot block i n)‖ /
        (1 + |(privateProductSheetRoot block i n : ℝ)|) ^ N := by
  let C := productReturnDenominatorConstant block i
  let c := (‖productSlabCornerValue s r‖ / 2) / (C * 2 ^ N)
  have hC : 0 < C := productReturnDenominatorConstant_pos block i
  have hJpos : 0 < ‖productSlabCornerValue s r‖ := norm_pos_iff.mpr hJ
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  filter_upwards [productSlabNumerator_privateRoot_eventually_lower s r
    (block.parameter i) (block.parameter_bounds i).1.le hJ] with n hn
  let x := privateProductSheetRoot block i n
  let B := |(quarterN (n + 5) : ℝ)|
  let G := ‖compactOriginalSheetTorusDerivative block (unitPhase x) (unitPhase (beta * x - 1 / 4))‖
  let w := (1 + |(x : ℝ)|) ^ N
  have hG : 0 < G := productPrivateReturn_derivative_norm_pos block i n
  have hGu : G ≤ C / B ^ (s - 1) := productPrivateReturn_derivative_norm_upper block i n
  have hw : 0 < w := by dsimp [w]; positivity
  have hwu : w ≤ 2 ^ N * B ^ N := privateProductSheetRoot_weight_upper block i n N
  have hB : 1 ≤ B := by linarith [privateReturn_denominator_lower n]
  have hBp : 0 < B := by linarith
  have hpow : B ^ N ≤ B ^ (s - 1) := pow_le_pow_right₀ hB hN
  have hden : G * w ≤ C * 2 ^ N := by
    calc
      _ ≤ (C / B ^ (s - 1)) * (2 ^ N * B ^ N) :=
        mul_le_mul hGu hwu hw.le (by positivity)
      _ ≤ (C / B ^ (s - 1)) * (2 ^ N * B ^ (s - 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
      _ = _ := by field_simp
  change c ≤ ‖productPhysicalResidue block r x‖ / w
  calc
    _ ≤ (‖productSlabCornerValue s r‖ / 2) / (G * w) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hG hw) hden
    _ ≤ ‖productSlabNumerator s r x‖ / (G * w) :=
      (div_le_div_iff_of_pos_right (mul_pos hG hw)).mpr hn
    _ = _ := by
      unfold productPhysicalResidue
      rw [norm_div, norm_neg, div_div]

/-- The original absolute physical series cannot be summable at low exponents. -/
theorem productPhysicalResidue_not_summable_lowExponent
    {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) (r : productNumeratorIndex s → ℂ)
    (hJ : productSlabCornerValue s r ≠ 0) (N : ℕ) (hN : N ≤ s - 1) :
    ¬ Summable (fun x : (compactOriginalProductSheetCarrier block).subtype =>
      ‖productPhysicalResidue block r x‖ / (1 + |(x : ℝ)|) ^ N) := by
  intro hs
  obtain ⟨c, hc, hlower⟩ := productPhysicalResidue_privateReturn_eventually_lower block i r hJ N hN
  have hzero : Tendsto (fun n => ‖productPhysicalResidue block r (privateProductSheetRoot block i n)‖ /
      (1 + |(privateProductSheetRoot block i n : ℝ)|) ^ N) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      hs.tendsto_cofinite_zero.comp (privateProductSheetRoot_tendsto_cofinite block i)
  obtain ⟨n, hlo, hhi⟩ := (hlower.and (hzero.eventually_lt_const hc)).exists
  linarith

/-- Exclusion concerns the actual original isolation coefficients of the
constructed tempered distribution, not a proxy coefficient sequence. -/
theorem productPhysicalDistribution_not_strongExponent
    {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) (r : productNumeratorIndex s → ℂ)
    (hJ : productSlabCornerValue s r ≠ 0) (N : ℕ) (hN : N ≤ s - 1) :
    productPhysicalDistribution block r ∉ stronglyTemperedAtomicAtExponent (compactOriginalProductSheetCarrier block) N := by
  intro h
  have hs := h.2
  change Summable (fun x : (compactOriginalProductSheetCarrier block).subtype =>
    ‖productPhysicalDistribution block r ((compactOriginalProductSheetCarrier block).isolationSchwartz x)‖ /
      (1 + |(x : ℝ)|) ^ N) at hs
  simp_rw [productPhysicalDistribution_isolation] at hs
  exact productPhysicalResidue_not_summable_lowExponent block i r hJ N hN hs

theorem productPhysicalDistribution_ne_zero
    {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) (r : productNumeratorIndex s → ℂ)
    (hJ : productSlabCornerValue s r ≠ 0) : productPhysicalDistribution block r ≠ 0 := by
  intro hz
  apply productPhysicalDistribution_not_strongExponent block i r hJ 0 (Nat.zero_le _)
  rw [hz]
  exact Submodule.zero_mem _

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
