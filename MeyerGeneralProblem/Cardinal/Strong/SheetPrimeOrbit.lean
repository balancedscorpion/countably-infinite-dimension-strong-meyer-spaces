module

public import MeyerGeneralProblem.Cardinal.Strong.SheetOrbitNorms
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

/-! A full centered root-of-unity polygon cannot lie on a complete original
real-parameter sheet product. The radius quadratic and strict half-plane identity
pay this fact even when the sheet count exceeds the prime orbit size. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The literal full primitive-root polygon retains distinct points and all coefficients. -/
theorem originalPrimitiveOrbit_injective {m : ℕ} {ζ U : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hU : U ≠ 0) :
    Function.Injective (fun t : Fin m => ζ ^ t.val * U) := by
  intro t v h
  exact Fin.ext (hζ.pow_inj t.isLt v.isLt (mul_right_cancel₀ hU h))

/-- The actual full centered polygon has zero sum, without an averaging certificate. -/
theorem originalPrimitiveOrbit_sum_zero {m : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hm : 1 < m) (U : ℂ) :
    ∑ t : Fin m, ζ ^ t.val * U = 0 := by
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range, hζ.geom_sum_eq_zero hm, zero_mul]

/-- EVERY affine first-coordinate orbit avoids the complete original sheet product.
No sheet-count bound or generic-position premise is used. -/
theorem originalSheetProduct_primitive_orbit_avoids {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i ∧ a i < 1)
    {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 3 ≤ m)
    (U V : ℂ) (hU : U ≠ 0) :
    ∃ t : Fin m, (∏ i : ι, sheetPolynomial (a i) (ζ ^ t.val * U) V) ≠ 0 := by
  classical
  by_contra! hzero
  have hr (t : Fin m) : ∃ i : ι, sheetPolynomial (a i) (ζ ^ t.val * U) V = 0 := by
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp (hzero t)
    exact ⟨i, hi⟩
  choose j hj using hr
  let t₀ : Fin m := ⟨0, by omega⟩
  let t₁ : Fin m := ⟨1, by omega⟩
  let t₂ : Fin m := ⟨2, by omega⟩
  have h01 : t₀ ≠ t₁ := by intro h; have := congrArg Fin.val h; norm_num [t₀, t₁] at this
  have h02 : t₀ ≠ t₂ := by intro h; have := congrArg Fin.val h; norm_num [t₀, t₂] at this
  have h12 : t₁ ≠ t₂ := by intro h; have := congrArg Fin.val h; norm_num [t₁, t₂] at this
  have hinj := originalPrimitiveOrbit_injective hζ hU
  have haj : Function.Injective (fun t => a (j t)) := by
    intro t v he
    change a (j t) = a (j v) at he
    apply hinj
    apply originalSheetRoot_unique_first (ha (j t)).1 (ha (j t)).2 (hj t)
    rw [he]
    exact hj v
  have hnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by omega)
  have hs (t : Fin m) : Complex.normSq (ζ ^ t.val * U) = Complex.normSq U := by
    simp only [Complex.normSq_eq_norm_sq, norm_mul, norm_pow, hnorm, one_pow, one_mul]
  obtain ⟨_, hV⟩ := originalSheetRoot_three_parameters_unit_radius
    (fun he => h01 (haj he)) (fun he => h02 (haj he)) (fun he => h12 (haj he))
    (Complex.normSq_nonneg U) (hj t₀) (hj t₁) (hj t₂) (hs t₀) (hs t₁) (hs t₂)
  by_cases hi : V.im = 0
  · have hfirst (t : Fin m) : ζ ^ t.val * U = V :=
      originalSheetRoot_real_unit_first (ha (j t)).1 (ha (j t)).2 (hj t) hV hi
    exact h01 (hinj ((hfirst t₀).trans (hfirst t₁).symm))
  · have hneg : (∑ t : Fin m, (ζ ^ t.val * U).im * V.im) < 0 :=
      Finset.sum_neg (fun t _ => originalSheetRoot_imag_opposite
        (ha (j t)).1 (ha (j t)).2 (hj t) hi) ⟨t₀, Finset.mem_univ _⟩
    have hz : (∑ t : Fin m, (ζ ^ t.val * U).im * V.im) = 0 := by
      rw [← Finset.sum_mul]
      change (∑ t : Fin m, Complex.imAddGroupHom (ζ ^ t.val * U)) * V.im = 0
      rw [← map_sum]
      change (∑ t : Fin m, ζ ^ t.val * U).im * V.im = 0
      rw [originalPrimitiveOrbit_sum_zero hζ (by omega)]
      simp
    rw [hz] at hneg
    exact lt_irrefl _ hneg

end
end MeyerGeneralProblem.StrongParity
