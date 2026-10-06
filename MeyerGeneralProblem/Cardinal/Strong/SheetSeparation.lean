module

public import MeyerGeneralProblem.Cardinal.Strong.PhaseDistance
public import MeyerGeneralProblem.Cardinal.Strong.ParityBarrier

@[expose] public section

/-!
# Polynomial separation at actual roots of the original sheets

The two algebraic corners are both retained. The inhomogeneous parity
barrier forces the original phase difference to be bounded below by a
constant times `1 / (1 + |x|)` at every sheet root.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem sheet_root_corner_product {a Z W : ℂ} (hroot : sheetPolynomial a Z W = 0) :
    (Z - W) * (W - a) = 1 - W ^ 2 := by
  dsimp [sheetPolynomial] at hroot
  linear_combination -hroot

/-- A root is close to at least one of the two structural corners. -/
theorem sheet_root_near_corner {a Z W : ℂ} (ha : ‖a‖ ≤ 1) (hW : ‖W‖ = 1)
    (hroot : sheetPolynomial a Z W = 0) :
    (‖W - 1‖ ≤ 2 * ‖Z - W‖ ∧ ‖Z - 1‖ ≤ 3 * ‖Z - W‖) ∨
    (‖W + 1‖ ≤ 2 * ‖Z - W‖ ∧ ‖Z + 1‖ ≤ 3 * ‖Z - W‖) := by
  have hWa : ‖W - a‖ ≤ 2 := by
    calc
      _ ≤ ‖W‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [hW]; linarith
  have hprod : ‖W - 1‖ * ‖W + 1‖ ≤ 2 * ‖Z - W‖ := by
    have hid : (W - 1) * (W + 1) = -(1 - W ^ 2) := by ring
    rw [← norm_mul, hid, norm_neg, ← sheet_root_corner_product hroot, norm_mul]
    nlinarith [norm_nonneg (Z - W)]
  have hsum : 2 ≤ ‖W - 1‖ + ‖W + 1‖ := by
    have h := norm_sub_le (W - 1) (W + 1)
    norm_num [show (W - 1) - (W + 1) = (-2 : ℂ) by ring] at h
    exact h
  by_cases hcmp : ‖W - 1‖ ≤ ‖W + 1‖
  · have hmax : 1 ≤ ‖W + 1‖ := by linarith
    have hmin : ‖W - 1‖ ≤ 2 * ‖Z - W‖ := by
      nlinarith [norm_nonneg (W - 1)]
    refine Or.inl ⟨hmin, ?_⟩
    calc
      _ ≤ ‖Z - W‖ + ‖W - 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith
  · have hmax : 1 ≤ ‖W - 1‖ := by linarith
    have hmin : ‖W + 1‖ ≤ 2 * ‖Z - W‖ := by
      nlinarith [norm_nonneg (W + 1)]
    refine Or.inr ⟨hmin, ?_⟩
    calc
      _ = ‖(Z - W) + (W + 1)‖ := by congr 1; ring
      _ ≤ ‖Z - W‖ + ‖W + 1‖ := norm_add_le _ _
      _ ≤ _ := by linarith

/-- A harmless weakening also covers the zero integer representative. -/
theorem parity_barrier_with_zero {k u : ℤ} (hu : Odd u) :
    1 / (4 * (1 + |(k : ℝ)|)) ≤ |2 * (k : ℝ) * beta - u| := by
  by_cases hk : k = 0
  · subst k
    have hu0 : u ≠ 0 := by intro h; subst u; norm_num at hu
    have huabs : (1 : ℤ) ≤ |u| := by
      have := abs_pos.mpr hu0
      omega
    have huabsR : (1 : ℝ) ≤ |(u : ℝ)| := by exact_mod_cast huabs
    norm_num
    linarith
  · calc
      _ ≤ 1 / (4 * |(k : ℝ)|) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      _ ≤ _ := parity_barrier hk hu

/-- Rounding near either corner yields the original odd phase estimate. -/
theorem quarterFlow_near_corner_lower (x : ℝ) (e : ℤ) {q : ℝ} (hq : 0 ≤ q)
    (hZ : ‖unitPhase x - unitPhase ((e : ℝ) / 2)‖ ≤ 3 * q)
    (hW : ‖unitPhase (beta * x - 1 / 4) - unitPhase ((e : ℝ) / 2)‖ ≤ 2 * q) :
    1 / (8 * (3 * beta + 2) * (1 + |x|)) ≤ q := by
  obtain ⟨j, hj, hjhalf⟩ := unitPhase_nearest_translate x ((e : ℝ) / 2)
  obtain ⟨i, hi, _⟩ := unitPhase_nearest_translate (beta * x - 1 / 4) ((e : ℝ) / 2)
  let k : ℤ := 2 * j + e
  let l : ℤ := 2 * i + e
  have hkcast : (k : ℝ) / 2 = (j : ℝ) + (e : ℝ) / 2 := by
    dsimp [k]; push_cast; ring
  have hlcast : (l : ℝ) / 2 = (i : ℝ) + (e : ℝ) / 2 := by
    dsimp [l]; push_cast; ring
  rw [← hkcast] at hj hjhalf
  rw [← hlcast] at hi
  have hjq : |x - (k : ℝ) / 2| ≤ 3 * q / 4 := by linarith
  have hiq : |beta * x - 1 / 4 - (l : ℝ) / 2| ≤ q / 2 := by linarith
  have hbeta : 0 < beta := (by linarith [beta_between_three_four] : 0 < beta)
  have hid : 2 * (k : ℝ) * beta - (2 * l + 1 : ℤ) =
      -4 * beta * (x - (k : ℝ) / 2) +
        4 * (beta * x - 1 / 4 - (l : ℝ) / 2) := by push_cast; ring
  have herror : |2 * (k : ℝ) * beta - (2 * l + 1 : ℤ)| ≤ (3 * beta + 2) * q := by
    rw [hid]
    calc
      _ ≤ |-4 * beta * (x - (k : ℝ) / 2)| +
          |4 * (beta * x - 1 / 4 - (l : ℝ) / 2)| := abs_add_le _ _
      _ = 4 * beta * |x - (k : ℝ) / 2| +
          4 * |beta * x - 1 / 4 - (l : ℝ) / 2| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hbeta]
        norm_num
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hjq hbeta.le]
  have hkbound : |(k : ℝ)| ≤ 2 * |x| + 1 := by
    have hidk : (k : ℝ) = 2 * x - 2 * (x - (k : ℝ) / 2) := by ring
    calc
      _ = |2 * x - 2 * (x - (k : ℝ) / 2)| := congrArg abs hidk
      _ ≤ |2 * x| + |2 * (x - (k : ℝ) / 2)| := abs_sub _ _
      _ ≤ _ := by rw [abs_mul, abs_mul]; norm_num; linarith
  have hu : Odd (2 * l + 1) := ⟨l, by ring⟩
  have hbar := (parity_barrier_with_zero (k := k) hu).trans herror
  have hdenpos : 0 < 4 * (1 + |(k : ℝ)|) := by positivity
  have hone : 1 ≤ 4 * (1 + |(k : ℝ)|) * ((3 * beta + 2) * q) := by
    have := (div_le_iff₀ hdenpos).mp hbar
    nlinarith
  have hden : 4 * (1 + |(k : ℝ)|) ≤ 8 * (1 + |x|) := by linarith
  have hbig := hone.trans (mul_le_mul_of_nonneg_right hden
    (mul_nonneg (by linarith) hq))
  apply (div_le_iff₀ (by positivity : 0 < 8 * (3 * beta + 2) * (1 + |x|))).mpr
  nlinarith

/-- The literal denominator separation needed for the strong mass bound. -/
theorem quarterFlow_sheet_separation {a : ℂ} (ha : ‖a‖ ≤ 1) (x : ℝ)
    (hroot : sheetPolynomial a (unitPhase x) (unitPhase (beta * x - 1 / 4)) = 0) :
    1 / (8 * (3 * beta + 2) * (1 + |x|)) ≤
      ‖unitPhase x - unitPhase (beta * x - 1 / 4)‖ := by
  have hzero : unitPhase (0 : ℝ) = 1 := by simp [unitPhase]
  have hhalf : unitPhase (1 / 2 : ℝ) = -1 := by
    unfold unitPhase
    norm_num [show 2 * Real.pi * (1 / 2) = Real.pi by ring]
  rcases sheet_root_near_corner ha (unitPhase_norm _) hroot with ⟨hw, hz⟩ | ⟨hw, hz⟩
  · apply quarterFlow_near_corner_lower x 0 (norm_nonneg _)
    · simpa [hzero] using hz
    · simpa [hzero] using hw
  · apply quarterFlow_near_corner_lower x 1 (norm_nonneg _)
    · norm_num only [Int.cast_one, hhalf, sub_neg_eq_add]
      exact hz
    · norm_num only [Int.cast_one, hhalf, sub_neg_eq_add]
      exact hw

end

end MeyerGeneralProblem.StrongParity
