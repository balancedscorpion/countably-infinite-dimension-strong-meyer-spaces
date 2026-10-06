module

public import MeyerGeneralProblem.Cardinal.Strong.SheetPrimeOrbit

@[expose] public section

/-! Full homogeneous coordinate coverage of the original divisor-orbit avoidance
argument. Both affine axes, both infinity edges and every corner are retained;
there is no disjoint-divisor or generic-position assumption. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The literal homogeneous original sheet, before inserting native powers and quarter phase. -/
def originalHomogeneousSheet (a : ℝ) (A B C D : ℂ) : ℂ :=
  A * C - a * A * D + a * B * C - B * D

/-- Exact affine normalization on the genuine nonzero chart coordinates. -/
theorem originalHomogeneousSheet_affine (a : ℝ) (A B C D : ℂ) (hA : A ≠ 0) (hC : C ≠ 0) :
    originalHomogeneousSheet a A B C D = A * C * sheetPolynomial a (B / A) (D / C) := by
  unfold originalHomogeneousSheet sheetPolynomial
  field_simp
  <;> ring

/-- A full centered primitive orbit has a point in each weak real half-plane. -/
theorem originalPrimitiveOrbit_real_halfplanes {m : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hm : 1 < m) (U : ℂ) :
    (∃ t : Fin m, (ζ ^ t.val * U).re ≤ 0) ∧ (∃ t : Fin m, 0 ≤ (ζ ^ t.val * U).re) := by
  classical
  let t₀ : Fin m := ⟨0, by omega⟩
  have hs : (∑ t : Fin m, (ζ ^ t.val * U).re) = 0 := by
    change (∑ t : Fin m, Complex.reAddGroupHom (ζ ^ t.val * U)) = 0
    rw [← map_sum]
    change (∑ t : Fin m, ζ ^ t.val * U).re = 0
    rw [originalPrimitiveOrbit_sum_zero hζ hm]
    rfl
  constructor
  · by_contra! h
    have hh := Finset.sum_pos (fun t _ => h t) ⟨t₀, Finset.mem_univ _⟩
    rw [hs] at hh
    exact lt_irrefl _ hh
  · by_contra! h
    have hh := Finset.sum_neg (fun t _ => h t) ⟨t₀, Finset.mem_univ _⟩
    rw [hs] at hh
    exact lt_irrefl _ hh

/-- The complete homogeneous orbit avoids EVERY nonzero coordinate pair, including
all four corners and all chart boundaries. Only literal real parameter bounds are used. -/
theorem originalHomogeneousSheetProduct_primitive_orbit_avoids {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i ∧ a i < 1)
    {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 3 ≤ m)
    (A B C D : ℂ) (hAB : A ≠ 0 ∨ B ≠ 0) (hCD : C ≠ 0 ∨ D ≠ 0) :
    ∃ t u : Fin m, (∏ i : ι, originalHomogeneousSheet (a i) A (ζ ^ t.val * B)
      C (ζ ^ u.val * D)) ≠ 0 := by
  classical
  let t₀ : Fin m := ⟨0, by omega⟩
  have hz : ζ ^ t₀.val = 1 := by simp [t₀]
  by_cases hA : A = 0
  · have hB : B ≠ 0 := hAB.resolve_left (not_ne_iff.mpr hA)
    by_cases hC : C = 0
    · have hD : D ≠ 0 := hCD.resolve_left (not_ne_iff.mpr hC)
      refine ⟨t₀, t₀, Finset.prod_ne_zero_iff.mpr ?_⟩
      intro i _
      simp only [originalHomogeneousSheet, hA, hC, hz, zero_mul, mul_zero, sub_zero,
        zero_add, one_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero hB hD
    · obtain ⟨u, hu⟩ := (originalPrimitiveOrbit_real_halfplanes hζ (by omega) (D / C)).1
      refine ⟨t₀, u, Finset.prod_ne_zero_iff.mpr ?_⟩
      intro i _
      have hr : (a i : ℂ) - ζ ^ u.val * (D / C) ≠ 0 := by
        intro h
        have hh := congrArg Complex.re (sub_eq_zero.mp h)
        simp only [Complex.ofReal_re] at hh
        linarith [(ha i).1]
      have he : originalHomogeneousSheet (a i) A (ζ ^ t₀.val * B) C (ζ ^ u.val * D) =
          B * C * ((a i : ℂ) - ζ ^ u.val * (D / C)) := by
        rw [hA, hz]
        unfold originalHomogeneousSheet
        field_simp
        <;> ring
      rw [he]
      exact mul_ne_zero (mul_ne_zero hB hC) hr
  · by_cases hC : C = 0
    · have hD : D ≠ 0 := hCD.resolve_left (not_ne_iff.mpr hC)
      obtain ⟨t, ht⟩ := (originalPrimitiveOrbit_real_halfplanes hζ (by omega) (B / A)).2
      refine ⟨t, t₀, Finset.prod_ne_zero_iff.mpr ?_⟩
      intro i _
      have hr : (a i : ℂ) + ζ ^ t.val * (B / A) ≠ 0 := by
        intro h
        have hh := congrArg Complex.re h
        simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hh
        linarith [(ha i).1]
      have he : originalHomogeneousSheet (a i) A (ζ ^ t.val * B) C (ζ ^ t₀.val * D) =
          -(A * D * ((a i : ℂ) + ζ ^ t.val * (B / A))) := by
        rw [hC, hz]
        unfold originalHomogeneousSheet
        field_simp
        <;> ring
      rw [he]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hA hD) hr)
    · by_cases hB : B = 0
      · obtain ⟨u, hu⟩ := (originalPrimitiveOrbit_real_halfplanes hζ (by omega) (D / C)).1
        refine ⟨t₀, u, Finset.prod_ne_zero_iff.mpr ?_⟩
        intro i _
        have hr : 1 - (a i : ℂ) * (ζ ^ u.val * (D / C)) ≠ 0 := by
          intro h
          have hh := congrArg Complex.re h
          simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hh
          have hn := mul_nonpos_of_nonneg_of_nonpos (ha i).1.le hu
          simp only [Complex.mul_re] at hn
          linarith
        have he : originalHomogeneousSheet (a i) A (ζ ^ t₀.val * B) C (ζ ^ u.val * D) =
            A * C * (1 - (a i : ℂ) * (ζ ^ u.val * (D / C))) := by
          rw [hB]
          unfold originalHomogeneousSheet
          field_simp
          <;> ring
        rw [he]
        exact mul_ne_zero (mul_ne_zero hA hC) hr
      · obtain ⟨t, ht⟩ := originalSheetProduct_primitive_orbit_avoids a ha hζ hm (B / A) (D / C)
          (div_ne_zero hB hA)
        refine ⟨t, t₀, Finset.prod_ne_zero_iff.mpr ?_⟩
        intro i _
        rw [originalHomogeneousSheet_affine _ _ _ _ _ hA hC, hz, one_mul, mul_div_assoc]
        exact mul_ne_zero (mul_ne_zero hA hC) (Finset.prod_ne_zero_iff.mp ht i (Finset.mem_univ _))

end
end MeyerGeneralProblem.StrongParity
