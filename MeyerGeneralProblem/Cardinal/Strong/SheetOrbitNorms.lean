module

public import MeyerGeneralProblem.Cardinal.Strong.ComplexSheetFlow

@[expose] public section

/-! Exact real quadratic and imaginary-part identities for the literal original
sheets. These pay the interior prime-orbit argument without a generic-position
or circle-intersection certificate. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- At any genuine sheet root, the Mobius denominator is nonzero. -/
theorem originalSheetRoot_denominator_ne_zero {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {Z W : ℂ} (h : sheetPolynomial a Z W = 0) : W - a ≠ 0 := by
  intro hd
  have hw := sub_eq_zero.mp hd
  rw [hw] at h
  have hr := congrArg Complex.re h
  simp [sheetPolynomial] at hr
  nlinarith

/-- A fixed original real parameter has only one first-coordinate root. -/
theorem originalSheetRoot_unique_first {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {Z Z' W : ℂ} (h : sheetPolynomial a Z W = 0) (h' : sheetPolynomial a Z' W = 0) : Z = Z' := by
  have hp : (Z - Z') * (W - a) = 0 := by
    unfold sheetPolynomial at h h'
    linear_combination h' - h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (originalSheetRoot_denominator_ne_zero ha ha1 h))

/-- Three distinct real roots force EVERY coefficient of the actual radius quadratic to vanish. -/
theorem originalRealQuadratic_three_roots (A B C a b c : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : A * a ^ 2 + B * a + C = 0)
    (hb : A * b ^ 2 + B * b + C = 0)
    (hc : A * c ^ 2 + B * c + C = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have hab' : (a - b) * (A * (a + b) + B) = 0 := by linear_combination ha - hb
  have hac' : (a - c) * (A * (a + c) + B) = 0 := by linear_combination ha - hc
  have eab := (mul_eq_zero.mp hab').resolve_left (sub_ne_zero.mpr hab)
  have eac := (mul_eq_zero.mp hac').resolve_left (sub_ne_zero.mpr hac)
  have eh : A * (b - c) = 0 := by linear_combination eab - eac
  have hA := (mul_eq_zero.mp eh).resolve_right (sub_ne_zero.mpr hbc)
  have hB : B = 0 := by simpa [hA] using eab
  have hC : C = 0 := by simpa [hA, hB] using ha
  exact ⟨hA, hB, hC⟩

/-- Each actual sheet root lies on the exact real radius quadratic in its parameter. -/
theorem originalSheetRoot_radius_quadratic {a r : ℝ} {Z W : ℂ}
    (h : sheetPolynomial a Z W = 0) (hr : Complex.normSq Z = r) :
    (Complex.normSq W - r) * a ^ 2 +
      (2 * W.re * (r - 1)) * a + (1 - r * Complex.normSq W) = 0 := by
  have hn := sheet_root_normSq h
  rw [hr] at hn
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im] at hn ⊢
  linear_combination -hn

/-- Three distinct original parameters at one circle radius force BOTH radii to be one. -/
theorem originalSheetRoot_three_parameters_unit_radius {a b c r : ℝ} {Z₁ Z₂ Z₃ W : ℂ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hr : 0 ≤ r)
    (h₁ : sheetPolynomial a Z₁ W = 0) (h₂ : sheetPolynomial b Z₂ W = 0)
    (h₃ : sheetPolynomial c Z₃ W = 0)
    (hr₁ : Complex.normSq Z₁ = r) (hr₂ : Complex.normSq Z₂ = r) (hr₃ : Complex.normSq Z₃ = r) :
    r = 1 ∧ Complex.normSq W = 1 := by
  obtain ⟨hA, _, hC⟩ := originalRealQuadratic_three_roots
    (Complex.normSq W - r) (2 * W.re * (r - 1)) (1 - r * Complex.normSq W)
    a b c hab hac hbc (originalSheetRoot_radius_quadratic h₁ hr₁)
    (originalSheetRoot_radius_quadratic h₂ hr₂) (originalSheetRoot_radius_quadratic h₃ hr₃)
  constructor <;> nlinarith [Complex.normSq_nonneg W]

/-- Exact imaginary-part product identity, with no division or circle assumption. -/
theorem originalSheetRoot_imag_product {a : ℝ} {Z W : ℂ} (h : sheetPolynomial a Z W = 0) :
    Complex.normSq (W - a) * Z.im = (a ^ 2 - 1) * W.im := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [sheetPolynomial, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.zero_re] at hr
  simp only [sheetPolynomial, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_im, Complex.zero_im] at hi
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  linear_combination W.im * hr - (W.re - a) * hi

/-- A real unit-circle companion pins every original sheet root to that companion. -/
theorem originalSheetRoot_real_unit_first {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {Z W : ℂ} (h : sheetPolynomial a Z W = 0)
    (hW : Complex.normSq W = 1) (hi : W.im = 0) : Z = W := by
  have hr : W.re ^ 2 = 1 := by simpa [Complex.normSq_apply, hi, pow_two] using hW
  have hw : W = 1 ∨ W = -1 := by
    rcases sq_eq_one_iff.mp hr with hpos | hneg
    · exact Or.inl (Complex.ext (by simpa using hpos) (by simpa using hi))
    · exact Or.inr (Complex.ext (by simpa using hneg) (by simpa using hi))
  have hc : sheetPolynomial a W W = 0 := by rcases hw with hw | hw <;> simp [hw, sheetPolynomial]
  exact originalSheetRoot_unique_first ha ha1 h hc

/-- Every genuine original sheet root has strictly opposite imaginary sign whenever
the companion is nonreal. This excludes a full centered polygon of roots. -/
theorem originalSheetRoot_imag_opposite {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {Z W : ℂ} (h : sheetPolynomial a Z W = 0) (hi : W.im ≠ 0) : Z.im * W.im < 0 := by
  have hd : 0 < Complex.normSq (W - a) :=
    Complex.normSq_pos.mpr (originalSheetRoot_denominator_ne_zero ha ha1 h)
  have he := originalSheetRoot_imag_product h
  have hn : a ^ 2 - 1 < 0 := by nlinarith
  have hs : (a ^ 2 - 1) * W.im ^ 2 < 0 := mul_neg_of_neg_of_pos hn (sq_pos_of_ne_zero hi)
  have hm : Complex.normSq (W - a) * (Z.im * W.im) < 0 := by
    calc
      _ = (a ^ 2 - 1) * W.im ^ 2 := by rw [← mul_assoc, he]; ring
      _ < 0 := hs
  by_contra hn
  have hnon := mul_nonneg hd.le (le_of_not_gt hn)
  linarith

end
end MeyerGeneralProblem.StrongParity
