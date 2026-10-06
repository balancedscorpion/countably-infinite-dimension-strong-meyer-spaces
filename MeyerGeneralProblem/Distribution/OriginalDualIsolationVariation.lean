module

public import MeyerGeneralProblem.Distribution.OriginalIsolationC0Tests
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-! The norm of the ACTUAL product-C0 dual controls the absolute sum of BOTH
original isolation observations. Finite phase tests are constructed internally;
no summability or variation-recovery certificate is an input. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty

/-- The genuine physical C0 record of an actual product weak dual. -/
def originalDualPhysicalC0Record (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) : StrongDual ℂ C₀(ℝ, ℂ) :=
  (WeakDual.toStrongDual q).comp ((ContinuousLinearMap.id ℂ C₀(ℝ, ℂ)).prod 0)

/-- The genuine spectral C0 record of the SAME actual product weak dual. -/
def originalDualSpectralC0Record (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) : StrongDual ℂ C₀(ℝ, ℂ) :=
  (WeakDual.toStrongDual q).comp ((0 : C₀(ℝ, ℂ) →L[ℂ] C₀(ℝ, ℂ)).prod (ContinuousLinearMap.id ℂ C₀(ℝ, ℂ)))

/-- ALL physical C0 record observations are literal first-component observations. -/
theorem originalDualPhysicalC0Record_apply (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (g : C₀(ℝ, ℂ)) :
    originalDualPhysicalC0Record q g = q (g, 0) := rfl

/-- ALL spectral C0 record observations are literal second-component observations. -/
theorem originalDualSpectralC0Record_apply (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (g : C₀(ℝ, ℂ)) :
    originalDualSpectralC0Record q g = q (0, g) := rfl

/-- An actual finite phase test evaluates EXACTLY the absolute sum of its genuine C0 observations. -/
theorem originalFiniteIsolationC0_phase_eval (S : LocallyFiniteCarrier) (E : Finset S.subtype)
    (u : StrongDual ℂ C₀(ℝ, ℂ)) :
    u (originalFiniteIsolationC0 S E (fun x => originalCoefficientPhase (u (originalIsolationC0 S x)))) =
      ((∑ x ∈ E, ‖u (originalIsolationC0 S x)‖) : ℂ) := by
  rw [originalFiniteIsolationC0, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_comm]
  exact originalCoefficientPhase_mul _

/-- The actual product max norm controls the SUM of BOTH finite original isolation masses. -/
theorem originalDualIsolation_finite_pair_mass_le_norm (S : LocallyFiniteCarrier)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) (E : Finset S.subtype) :
    (∑ x ∈ E, ‖q (originalIsolationC0 S x, 0)‖) +
      (∑ x ∈ E, ‖q (0, originalIsolationC0 S x)‖) ≤ ‖WeakDual.toStrongDual q‖ := by
  let u := originalDualPhysicalC0Record q
  let v := originalDualSpectralC0Record q
  let g := originalFiniteIsolationC0 S E (fun x => originalCoefficientPhase (u (originalIsolationC0 S x)))
  let h := originalFiniteIsolationC0 S E (fun x => originalCoefficientPhase (v (originalIsolationC0 S x)))
  have hg : ‖g‖ ≤ 1 := originalFiniteIsolationC0_norm_le_one S E _
    (fun x hx => originalCoefficientPhase_norm_le_one _)
  have hh : ‖h‖ ≤ 1 := originalFiniteIsolationC0_norm_le_one S E _
    (fun x hx => originalCoefficientPhase_norm_le_one _)
  have he : q (g, h) =
      (((∑ x ∈ E, ‖q (originalIsolationC0 S x, 0)‖) +
        ∑ x ∈ E, ‖q (0, originalIsolationC0 S x)‖ : ℝ) : ℂ) := by
    calc
      _ = q (g, 0) + q (0, h) := by
        rw [← map_add]
        congr 1
        ext <;> simp
      _ = u g + v h := rfl
      _ = _ := by
        rw [originalFiniteIsolationC0_phase_eval, originalFiniteIsolationC0_phase_eval]
        simp only [u, v, originalDualPhysicalC0Record_apply, originalDualSpectralC0Record_apply,
          Complex.ofReal_add]
        push_cast
        rfl
  have hn := (WeakDual.toStrongDual q).le_opNorm (g, h)
  have hp : ‖(g, h)‖ ≤ 1 := norm_prod_le_iff.mpr ⟨hg, hh⟩
  have hb := hn.trans (mul_le_mul_of_nonneg_left hp (norm_nonneg (WeakDual.toStrongDual q)))
  rw [mul_one] at hb
  change ‖q (g, h)‖ ≤ _ at hb
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (add_nonneg (Finset.sum_nonneg (fun x hx => norm_nonneg _))
      (Finset.sum_nonneg (fun x hx => norm_nonneg _)))] at hb
  exact hb

/-- The genuine physical isolation observations are absolutely summable, derived from the actual dual norm. -/
theorem originalDualIsolation_physical_summable (S : LocallyFiniteCarrier)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) :
    Summable (fun x : S.subtype => ‖q (originalIsolationC0 S x, 0)‖) := by
  apply summable_of_sum_le (fun x => norm_nonneg _) (c := ‖WeakDual.toStrongDual q‖)
  intro E
  have h := originalDualIsolation_finite_pair_mass_le_norm S q E
  have hs : 0 ≤ ∑ x ∈ E, ‖q (0, originalIsolationC0 S x)‖ := Finset.sum_nonneg (fun x hx => norm_nonneg _)
  linarith

/-- The genuine spectral isolation observations are absolutely summable at the SAME actual dual scale. -/
theorem originalDualIsolation_spectral_summable (S : LocallyFiniteCarrier)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) :
    Summable (fun x : S.subtype => ‖q (0, originalIsolationC0 S x)‖) := by
  apply summable_of_sum_le (fun x => norm_nonneg _) (c := ‖WeakDual.toStrongDual q‖)
  intro E
  have h := originalDualIsolation_finite_pair_mass_le_norm S q E
  have hp : 0 ≤ ∑ x ∈ E, ‖q (originalIsolationC0 S x, 0)‖ := Finset.sum_nonneg (fun x hx => norm_nonneg _)
  linarith

/-- BOTH COMPLETE sums of absolute isolation observations are bounded by the ACTUAL pair dual norm. -/
theorem originalDualIsolation_pair_mass_le_norm (S : LocallyFiniteCarrier)
    (q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) :
    (∑' x : S.subtype, ‖q (originalIsolationC0 S x, 0)‖) +
      (∑' x : S.subtype, ‖q (0, originalIsolationC0 S x)‖) ≤ ‖WeakDual.toStrongDual q‖ := by
  rw [← Summable.tsum_add (originalDualIsolation_physical_summable S q)
    (originalDualIsolation_spectral_summable S q)]
  apply Real.tsum_le_of_sum_le (fun x => add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro E
  rw [Finset.sum_add_distrib]
  exact originalDualIsolation_finite_pair_mass_le_norm S q E

end
end MeyerGeneralProblem
