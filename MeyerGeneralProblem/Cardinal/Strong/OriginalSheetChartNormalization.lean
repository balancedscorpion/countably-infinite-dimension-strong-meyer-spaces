module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalChartNumerators

@[expose] public section

/-! Literal four-chart normalization of genuine phased native sheets.
One reversed coordinate uses the reciprocal parameter; both reversed
coordinates restore the original parameter. All scalars are retained. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Exactly one reversed coordinate reciprocates the original real sheet parameter. -/
def originalSheetChartParameter (c : Bool × Bool) (a : ℝ) : ℝ :=
  if c.1 = c.2 then a else a⁻¹

/-- Only a reversed first native coordinate inverts its original phase. -/
def originalSheetChartFirstPhase (c : Bool × Bool) (ρ : ℂ) : ℂ :=
  if c.1 then ρ⁻¹ else ρ

/-- Only a reversed second native coordinate inverts its original phase AFTER the native power. -/
def originalSheetChartSecondPhase (c : Bool × Bool) (σ : ℂ) : ℂ :=
  if c.2 then σ⁻¹ else σ

/-- The literal nonzero sheet normalization scalar on the selected projective chart. -/
def originalSheetChartScalar (c : Bool × Bool) (a : ℝ) (ρ σ : ℂ) : ℂ :=
  if c.1 then (if c.2 then -(ρ * σ) else (a : ℂ) * ρ)
  else (if c.2 then -((a : ℂ) * σ) else 1)

/-- Original positive parameters stay positive and nondegenerate on ALL four charts,
including the reciprocal parameter outside the old interval. -/
theorem originalSheetChartParameter_nondegenerate (c : Bool × Bool) (a : ℝ)
    (ha : 0 < a ∧ a < 1) :
    0 < originalSheetChartParameter c a ∧
      (originalSheetChartParameter c a : ℂ) ≠ 0 ∧ (originalSheetChartParameter c a : ℂ) ^ 2 ≠ 1 := by
  have h := originalSheetParameter_nondegenerate a ha
  have hr : ((a⁻¹ : ℝ) : ℂ) ^ 2 ≠ 1 := by
    intro he
    have hi : ((a : ℂ) ^ 2)⁻¹ = (1 : ℂ)⁻¹ := by
      simpa only [Complex.ofReal_inv, inv_pow, inv_one] using he
    exact h.2 (inv_injective hi)
  rcases c with ⟨b, e⟩
  cases b <;> cases e <;> simp only [originalSheetChartParameter, Bool.false_eq_true, Bool.true_eq_false,
    ite_true, ite_false]
  · exact ⟨ha.1, h⟩
  · exact ⟨inv_pos.mpr ha.1, by simpa only [Complex.ofReal_inv] using inv_ne_zero h.1, hr⟩
  · exact ⟨inv_pos.mpr ha.1, by simpa only [Complex.ofReal_inv] using inv_ne_zero h.1, hr⟩
  · exact ⟨ha.1, h⟩

/-- The selected reciprocal-or-original parameter preserves equality of actual parameters exactly. -/
theorem originalSheetChartParameter_injective (c : Bool × Bool) :
    Function.Injective (originalSheetChartParameter c) := by
  intro a b h
  by_cases hc : c.1 = c.2
  · simpa [originalSheetChartParameter, hc] using h
  · have hi : a⁻¹ = b⁻¹ := by simpa [originalSheetChartParameter, hc] using h
    exact inv_injective hi

/-- Chart phase inversion never erases a genuine nonzero native phase. -/
theorem originalSheetChartPhases_ne_zero (c : Bool × Bool) (ρ σ : ℂ) (hρ : ρ ≠ 0) (hσ : σ ≠ 0) :
    originalSheetChartFirstPhase c ρ ≠ 0 ∧ originalSheetChartSecondPhase c σ ≠ 0 := by
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> simp [originalSheetChartFirstPhase, originalSheetChartSecondPhase, hρ, hσ]

/-- The actual four-chart scalar is nonzero using ONLY nonzero original parameter and phases. -/
theorem originalSheetChartScalar_ne_zero (c : Bool × Bool) (a : ℝ) (ρ σ : ℂ)
    (ha : a ≠ 0) (hρ : ρ ≠ 0) (hσ : σ ≠ 0) : originalSheetChartScalar c a ρ σ ≠ 0 := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rcases c with ⟨b, e⟩
  cases b <;> cases e <;> simp [originalSheetChartScalar, ha0, hρ, hσ]

/-- EXACT literal phased native sheet coefficients on ALL four charts, including zero native degree. -/
theorem originalPhasedPositiveSheetPolynomial_chart_normalization (c : Bool × Bool) (d : ℕ)
    (a : ℝ) (ρ σ : ℂ) (ha : a ≠ 0) (hρ : ρ ≠ 0) (hσ : σ ≠ 0) :
    originalPositiveChartReflection c d (originalPhasedPositiveSheetPolynomial d a ρ σ) =
      originalSheetChartScalar c a ρ σ • originalPhasedPositiveSheetPolynomial d
        (originalSheetChartParameter c a) (originalSheetChartFirstPhase c ρ) (originalSheetChartSecondPhase c σ) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rcases c with ⟨b, e⟩
  cases b <;> cases e <;>
    simp only [originalPhasedPositiveSheetPolynomial, map_sub, map_add, originalPositiveChartReflection_single,
      originalChartNativeIndex, originalSheetChartScalar, originalSheetChartParameter,
      originalSheetChartFirstPhase, originalSheetChartSecondPhase, Bool.false_eq_true,
      Bool.true_eq_false, ite_true, ite_false, Nat.sub_self, Nat.sub_zero]
  all_goals
    ext n
    simp only [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_smul,
      AddMonoidAlgebra.coeff_single, Finsupp.smul_apply, smul_eq_mul, Finsupp.sub_apply,
      Finsupp.add_apply, Finsupp.single_apply, Complex.ofReal_inv]
    split_ifs <;> field_simp [ha0, hρ, hσ] <;> ring

/-- The already proved generic complex Eisenstein theorem covers ANY real nondegenerate parameter. -/
theorem originalPhasedPositiveSheetPolynomial_prime_of_nondegenerate (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ha0 : (a : ℂ) ≠ 0) (ha2 : (a : ℂ) ^ 2 ≠ 1)
    (ρ σ : ℂ) (hρ : ρ ≠ 0) (hσ : σ ≠ 0) :
    Prime (originalPhasedPositiveSheetPolynomial d a ρ σ) := by
  rw [← MulEquiv.prime_iff originalPositiveIteratedEquiv, originalPositiveIteratedEquiv_phased_sheet]
  exact (originalSheetIteratedPolynomial_irreducible d hd (a : ℂ) ρ σ ha0 ha2 hρ hσ).prime

/-- A nonzero complex scalar is a unit in the genuine original positive polynomial algebra. -/
theorem originalPositivePolynomial_constant_isUnit (z : ℂ) (hz : z ≠ 0) :
    IsUnit (algebraMap ℂ (AddMonoidAlgebra ℂ (ℕ × ℕ)) z) :=
  (isUnit_iff_ne_zero.mpr hz).map (algebraMap ℂ (AddMonoidAlgebra ℂ (ℕ × ℕ)))

/-- EVERY fixed chart of an actual nondegenerate sheet remains prime, with reciprocal primality and scalar internal. -/
theorem originalPhasedPositiveSheetPolynomial_chart_prime (c : Bool × Bool) (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ha : 0 < a ∧ a < 1) (ρ σ : ℂ) (hρ : ρ ≠ 0) (hσ : σ ≠ 0) :
    Prime (originalPositiveChartReflection c d (originalPhasedPositiveSheetPolynomial d a ρ σ)) := by
  have hac := originalSheetChartParameter_nondegenerate c a ha
  have hph := originalSheetChartPhases_ne_zero c ρ σ hρ hσ
  have hp := originalPhasedPositiveSheetPolynomial_prime_of_nondegenerate d hd _ hac.2.1 hac.2.2 _ _ hph.1 hph.2
  have hu := originalPositivePolynomial_constant_isUnit _ (originalSheetChartScalar_ne_zero c a ρ σ ha.1.ne' hρ hσ)
  rw [originalPhasedPositiveSheetPolynomial_chart_normalization c d a ρ σ ha.1.ne' hρ hσ, Algebra.smul_def]
  exact (associated_unit_mul_right _ _ hu).prime hp

end
end MeyerGeneralProblem.StrongParity
