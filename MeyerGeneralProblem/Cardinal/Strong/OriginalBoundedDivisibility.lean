module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalGlobalSplitting

@[expose] public section

/-! Exact bounded divisibility in the original positive coefficient algebra.
Nonzero full-degree corners force a same-square quotient to be constant.
Origin or top-corner vanishing then forces the entire dividend to vanish. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual zero square contains only the literal constant coefficient. -/
theorem originalPositive_square_zero_constant (v : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hv : OriginalPositiveInSquare v 0) :
    v = AddMonoidAlgebra.single (0, 0) (v.coeff (0, 0)) := by
  classical
  ext n
  by_cases hn : n = (0, 0)
  · subst n; simp
  · have hc : v.coeff n = 0 := by
      by_contra hc
      have hb := hv n (Finsupp.mem_support_iff.mpr hc)
      apply hn
      exact Prod.ext (by omega) (by omega)
    simp [hc, hn]

/-- A genuine positive quotient of a full-corner divisor cannot exceed degree
zero when divisor and dividend have the SAME individual square bound. -/
theorem originalPositive_bounded_divisor_constant
    (q a : AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ℕ)
    (hq : OriginalPositiveInSquare q d) (ha : OriginalPositiveInSquare a d)
    (h0 : q.coeff (0, 0) ≠ 0) (hd : q.coeff (d, d) ≠ 0) (hdiv : q ∣ a) :
    ∃ c : ℂ, a = q * AddMonoidAlgebra.single (0, 0) c := by
  classical
  obtain ⟨v, hv⟩ := hdiv
  have hprod (swap : Bool) :
      ∀ n ∈ (originalPositiveLaurentEmbedding q * originalPositiveLaurentEmbedding v).coeff.support,
        (originalLaurentAxisIndex swap false n).1 ≤ (d : ℤ) := by
    intro n hn
    rw [← map_mul, ← hv, originalPositiveLaurentEmbedding_coeff,
      originalPositivePolynomialIntegerCoefficients_support] at hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hn
    have hb := ha p hp
    cases swap <;> simp only [originalLaurentAxisIndex, Bool.false_eq_true, reduceIte,
      originalNativeIntegerEmbedding_apply]
    all_goals exact_mod_cast (by first | exact hb.1 | exact hb.2)
  have hleft := originalLaurent_axis_bound_of_mul false false q d hq h0 hd
    (originalPositiveLaurentEmbedding v) (hprod false)
  have hright := originalLaurent_axis_bound_of_mul true false q d hq h0 hd
    (originalPositiveLaurentEmbedding v) (hprod true)
  have hbox : OriginalPositiveInSquare v 0 := by
    intro n hn
    have hz : originalNativeIntegerEmbedding n ∈ (originalPositiveLaurentEmbedding v).coeff.support := by
      apply Finsupp.mem_support_iff.mpr
      rw [originalPositiveLaurentEmbedding_coeff, originalPositivePolynomialIntegerCoefficients_apply]
      exact Finsupp.mem_support_iff.mp hn
    have hl := hleft _ hz
    have hr := hright _ hz
    change (n.1 : ℤ) ≤ 0 at hl
    change (n.2 : ℤ) ≤ 0 at hr
    constructor <;> omega
  exact ⟨v.coeff (0, 0), hv.trans (congrArg (fun p => q * p)
    (originalPositive_square_zero_constant v hbox))⟩

/-- A same-square divisible polynomial with zero origin coefficient is zero;
no quotient-constant certificate is an input. -/
theorem originalPositive_bounded_divisor_zero_origin
    (q a : AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ℕ)
    (hq : OriginalPositiveInSquare q d) (ha : OriginalPositiveInSquare a d)
    (h0 : q.coeff (0, 0) ≠ 0) (hd : q.coeff (d, d) ≠ 0)
    (hdiv : q ∣ a) (ha0 : a.coeff (0, 0) = 0) : a = 0 := by
  obtain ⟨c, hc⟩ := originalPositive_bounded_divisor_constant q a d hq ha h0 hd hdiv
  have hz : q.coeff (0, 0) * c = 0 := by
    rw [hc] at ha0
    change (q * AddMonoidAlgebra.single (0 : ℕ × ℕ) c).coeff (0, 0) = 0 at ha0
    rw [AddMonoidAlgebra.coeff_mul_single_zero] at ha0
    exact ha0
  have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_left h0
  simp [hc, hc0]

/-- The analogous top-corner anchor proves zero, retaining all other original
coefficients and their collisions. -/
theorem originalPositive_bounded_divisor_zero_top
    (q a : AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ℕ)
    (hq : OriginalPositiveInSquare q d) (ha : OriginalPositiveInSquare a d)
    (h0 : q.coeff (0, 0) ≠ 0) (hd : q.coeff (d, d) ≠ 0)
    (hdiv : q ∣ a) (hat : a.coeff (d, d) = 0) : a = 0 := by
  obtain ⟨c, hc⟩ := originalPositive_bounded_divisor_constant q a d hq ha h0 hd hdiv
  have hz : q.coeff (d, d) * c = 0 := by
    rw [hc] at hat
    change (q * AddMonoidAlgebra.single (0 : ℕ × ℕ) c).coeff (d, d) = 0 at hat
    rw [AddMonoidAlgebra.coeff_mul_single_zero] at hat
    exact hat
  have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_left hd
  simp [hc, hc0]

end
end MeyerGeneralProblem.StrongParity
