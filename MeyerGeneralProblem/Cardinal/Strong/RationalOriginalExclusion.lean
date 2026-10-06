module

public import MeyerGeneralProblem.Cardinal.Strong.RationalCoarseValue

@[expose] public section

/-! Computable exclusion data and actual binary residuals for accepted PREFIX Section 2.
Fixed constants are indices into earlier rational name programs. Their names
are inputs to this finite evaluator; the final recursive family is still unpaid.
-/

namespace MeyerGeneralProblem.StrongParity

/-- Ordinary original exclusion data, with fixed constants represented by name indices. -/
inductive ComputedRootExclusion where
  /-- An original root versus an encoded coarse value. -/
  | root (n : ℤ) (u v : ℚ)
  /-- An original label difference versus an encoded coarse value. -/
  | difference (n l : ℤ) (u v : ℚ)
  /-- An original label sum versus an encoded coarse value. -/
  | sum (n l : ℤ) (u v : ℚ)
  /-- An original root plus one earlier named constant versus another. -/
  | fixed (n : ℤ) (y gamma : ℕ)

/-- The literal ordinary finite rational residual program for all four equation types. -/
def ComputedRootExclusion.approx (names : ℕ → ℕ → ℚ) (m : ℕ) (a : ℚ) (p : ℕ) :
    ComputedRootExclusion → ℚ
  | .root n u v => rationalScaledOriginalRootApprox m n a (p + 2) - rationalCoarseApprox u v (p + 2)
  | .difference n l u v => if n = l then 1 else
      rationalScaledOriginalRootApprox m n a (p + 2) -
      rationalScaledOriginalRootApprox m l a (p + 2) - rationalCoarseApprox u v (p + 2)
  | .sum n l u v => rationalScaledOriginalRootApprox m n a (p + 2) +
      rationalScaledOriginalRootApprox m l a (p + 2) - rationalCoarseApprox u v (p + 2)
  | .fixed n y gamma => rationalScaledOriginalRootApprox m n a (p + 2) +
      names y (p + 2) - names gamma (p + 2)

/-- An exact rational positive-margin certificate for the computed residual. -/
def ComputedRootExclusion.certificate (names : ℕ → ℕ → ℚ) (m : ℕ) (a : ℚ) (p : ℕ)
    (code : ComputedRootExclusion) : Bool :=
  decide (rationalBinaryRadius p < |code.approx names m a p|)

/-- The rational lower margin emitted by the actual finite residual evaluator. -/
def ComputedRootExclusion.margin (names : ℕ → ℕ → ℚ) (m : ℕ) (a : ℚ) (p : ℕ)
    (code : ComputedRootExclusion) : ℚ :=
  |code.approx names m a p| - rationalBinaryRadius p

noncomputable section

/-- Map computational equation data to the already proved literal original semantics. -/
def ComputedRootExclusion.semantic (values : ℕ → ℝ) : ComputedRootExclusion → OriginalRootExclusion
  | .root n u v => .root n u v
  | .difference n l u v => .difference n l u v
  | .sum n l u v => .sum n l u v
  | .fixed n y gamma => .fixed n (values y) (values gamma)

private theorem sum_error {x y X Y ex ey : ℝ}
    (hx : |x - X| ≤ ex) (hy : |y - Y| ≤ ey) :
    |(x + y) - (X + Y)| ≤ ex + ey := by
  calc
    _ = |(x - X) + (y - Y)| := by congr 1; ring
    _ ≤ |x - X| + |y - Y| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

private theorem sub_error {x y X Y ex ey : ℝ}
    (hx : |x - X| ≤ ex) (hy : |y - Y| ≤ ey) :
    |(x - y) - (X - Y)| ≤ ex + ey := by
  calc
    _ = |(x - X) - (y - Y)| := by congr 1; ring
    _ ≤ |x - X| + |y - Y| := abs_sub _ _
    _ ≤ _ := add_le_add hx hy

private theorem three_binary_errors (p : ℕ) :
    1 / (2 : ℝ) ^ (p + 2) + 1 / (2 : ℝ) ^ (p + 2) +
      1 / (2 : ℝ) ^ (p + 2) ≤ 1 / (2 : ℝ) ^ p := by
  rw [pow_add]
  norm_num
  have hp : 0 ≤ ((2 : ℝ) ^ p)⁻¹ := by positivity
  simp only [div_eq_mul_inv]
  norm_num
  linarith

/-- All four implemented residuals approximate the ACTUAL original equations with binary error. -/
theorem ComputedRootExclusion.approx_error (names : ℕ → ℕ → ℚ) (values : ℕ → ℝ)
    (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) {a : ℚ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (p : ℕ) (code : ComputedRootExclusion) :
    |(code.approx names m a p : ℝ) - (code.semantic values).residual m a| ≤
      1 / (2 : ℝ) ^ p := by
  cases code with
  | root n u v =>
      simp only [ComputedRootExclusion.approx, ComputedRootExclusion.semantic,
        OriginalRootExclusion.residual, Rat.cast_sub]
      have h := sub_error (rationalScaledOriginalRootApprox_error m n ha ha2 (p + 2))
        (rationalCoarseApprox_error u v (p + 2))
      have ht := three_binary_errors p
      have hp : 0 ≤ 1 / (2 : ℝ) ^ (p + 2) := by positivity
      exact h.trans (by linarith)
  | difference n l u v =>
      by_cases hnl : n = l
      · simp only [ComputedRootExclusion.approx, ComputedRootExclusion.semantic,
          OriginalRootExclusion.residual, ite_eq_left hnl, Rat.cast_one, sub_self, abs_zero]
        positivity
      · simp only [ComputedRootExclusion.approx, ComputedRootExclusion.semantic,
          OriginalRootExclusion.residual, ite_eq_right hnl, Rat.cast_sub]
        exact (sub_error (sub_error (rationalScaledOriginalRootApprox_error m n ha ha2 (p + 2))
          (rationalScaledOriginalRootApprox_error m l ha ha2 (p + 2)))
          (rationalCoarseApprox_error u v (p + 2))).trans (three_binary_errors p)
  | sum n l u v =>
      simp only [ComputedRootExclusion.approx, ComputedRootExclusion.semantic,
        OriginalRootExclusion.residual, Rat.cast_sub, Rat.cast_add]
      exact (sub_error (sum_error (rationalScaledOriginalRootApprox_error m n ha ha2 (p + 2))
        (rationalScaledOriginalRootApprox_error m l ha ha2 (p + 2)))
        (rationalCoarseApprox_error u v (p + 2))).trans (three_binary_errors p)
  | fixed n y gamma =>
      simp only [ComputedRootExclusion.approx, ComputedRootExclusion.semantic,
        OriginalRootExclusion.residual, Rat.cast_sub, Rat.cast_add]
      exact (sub_error (sum_error (rationalScaledOriginalRootApprox_error m n ha ha2 (p + 2))
        (hname y (p + 2))) (hname gamma (p + 2))).trans (three_binary_errors p)

/-- The finite rational margin is a proved lower bound for the literal actual residual. -/
theorem ComputedRootExclusion.margin_le (names : ℕ → ℕ → ℚ) (values : ℕ → ℝ)
    (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) {a : ℚ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (p : ℕ) (code : ComputedRootExclusion) :
    (code.margin names m a p : ℝ) ≤ |(code.semantic values).residual m a| := by
  have h := code.approx_error names values hname m ha ha2 p
  have ht := abs_sub_abs_le_abs_sub (code.approx names m a p : ℝ)
    ((code.semantic values).residual m a)
  simp only [ComputedRootExclusion.margin, Rat.cast_sub, Rat.cast_abs, rationalBinaryRadius_cast]
  linarith

/-- The ordinary Boolean certificate is true exactly when its rational margin is positive. -/
theorem ComputedRootExclusion.certificate_iff (names : ℕ → ℕ → ℚ) (m : ℕ) (a : ℚ) (p : ℕ)
    (code : ComputedRootExclusion) :
    code.certificate names m a p = true ↔ 0 < code.margin names m a p := by
  simp only [ComputedRootExclusion.certificate, decide_eq_true_eq, ComputedRootExclusion.margin,
    sub_pos]

/-- Every successful rational certificate proves nonvanishing of the ACTUAL original equation. -/
theorem ComputedRootExclusion.certificate_sound (names : ℕ → ℕ → ℚ) (values : ℕ → ℝ)
    (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) {a : ℚ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (p : ℕ) (code : ComputedRootExclusion)
    (hc : code.certificate names m a p = true) : (code.semantic values).residual m a ≠ 0 := by
  have hp : (0 : ℝ) < (code.margin names m a p : ℝ) := by
    exact_mod_cast (code.certificate_iff names m a p).mp hc
  have h := code.margin_le names values hname m ha ha2 p
  intro hz
  rw [hz, abs_zero] at h
  linarith

end

end MeyerGeneralProblem.StrongParity
