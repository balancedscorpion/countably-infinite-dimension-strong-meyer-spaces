module

public import MeyerGeneralProblem.Distribution.OriginalWeightedDualCarrierConstraints

@[expose] public section

/-! Actual norm-one finite C0 tests from the original isolating Schwartz bumps.
The original half-radius supports are disjoint. Coefficient phases are
interpolated at ALL carrier points with norm at most one, derived internally. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty

/-- The original isolating Schwartz bump has norm at most one at EVERY real point. -/
theorem originalIsolationSchwartz_norm_le_one (S : LocallyFiniteCarrier) (x : S.subtype) (y : ℝ) :
    ‖S.isolationSchwartz x y‖ ≤ 1 := by
  change ‖((S.isolationBump x y : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (S.isolationBump x).nonneg]
  exact (S.isolationBump x).le_one

/-- Every nonzero value lies in the ACTUAL half-radius isolation ball. -/
theorem originalIsolationSchwartz_nonzero_dist (S : LocallyFiniteCarrier) (x : S.subtype) (y : ℝ)
    (hy : S.isolationSchwartz x y ≠ 0) : dist y (x : ℝ) < S.isolationRadius x / 2 := by
  have hb : S.isolationBump x y ≠ 0 := by
    intro h
    apply hy
    change ((S.isolationBump x y : ℝ) : ℂ) = 0
    rw [h]
    norm_num
  have hmem : y ∈ Function.support (S.isolationBump x) := hb
  rw [(S.isolationBump x).support_eq] at hmem
  exact Metric.mem_ball.mp hmem

/-- At EVERY real point at most ONE original isolation bump is nonzero. -/
theorem originalIsolationSchwartz_unique_nonzero (S : LocallyFiniteCarrier) (z : ℝ)
    (x y : S.subtype) (hx : S.isolationSchwartz x z ≠ 0) (hy : S.isolationSchwartz y z ≠ 0) : x = y := by
  by_contra hxy
  have hval : (x : ℝ) ≠ (y : ℝ) := fun h => hxy (Subtype.ext h)
  have hxz := originalIsolationSchwartz_nonzero_dist S x z hx
  have hyz := originalIsolationSchwartz_nonzero_dist S y z hy
  have hrx := S.isolationRadius_le_dist x y.property hval.symm
  have hry := S.isolationRadius_le_dist y x.property hval
  have ht := dist_triangle (x : ℝ) z (y : ℝ)
  rw [dist_comm (x : ℝ) z] at ht
  rw [dist_comm (y : ℝ) (x : ℝ)] at hrx
  linarith

/-- The ACTUAL original isolating bump as an ordinary C0 test. -/
def originalIsolationC0 (S : LocallyFiniteCarrier) (x : S.subtype) : C₀(ℝ, ℂ) :=
  (S.isolationSchwartz x).toZeroAtInfty

/-- Every ordinary isolating C0 value is the literal original Schwartz value. -/
theorem originalIsolationC0_apply (S : LocallyFiniteCarrier) (x : S.subtype) (y : ℝ) :
    originalIsolationC0 S x y = S.isolationSchwartz x y := rfl

/-- Every finite C0 sum evaluates by the literal finite sum of its values. -/
theorem originalC0_sum_apply {ι : Type*} (E : Finset ι) (u : ι → C₀(ℝ, ℂ)) (y : ℝ) :
    (∑ x ∈ E, u x) y = ∑ x ∈ E, u x y := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | @insert x E hx ih => simp only [Finset.sum_insert hx, ZeroAtInftyContinuousMap.add_apply, ih]

/-- The finite ACTUAL C0 interpolation test with the supplied finite coefficients. -/
def originalFiniteIsolationC0 (S : LocallyFiniteCarrier) (E : Finset S.subtype)
    (a : S.subtype → ℂ) : C₀(ℝ, ℂ) := ∑ x ∈ E, a x • originalIsolationC0 S x

/-- ALL carrier-point values of the actual finite interpolation are exact. -/
theorem originalFiniteIsolationC0_apply_subtype (S : LocallyFiniteCarrier) (E : Finset S.subtype)
    (a : S.subtype → ℂ) (y : S.subtype) :
    originalFiniteIsolationC0 S E a y = if y ∈ E then a y else 0 := by
  classical
  change (∑ x ∈ E, a x • originalIsolationC0 S x) (y : ℝ) = _
  rw [show (∑ x ∈ E, a x • originalIsolationC0 S x) (y : ℝ) =
    ∑ x ∈ E, a x * S.isolationSchwartz x y by
      simp only [originalC0_sum_apply, ZeroAtInftyContinuousMap.smul_apply,
        originalIsolationC0_apply, smul_eq_mul]]
  simp only [S.isolationSchwartz_apply_subtype]
  by_cases hy : y ∈ E
  · rw [Finset.sum_eq_single y]
    · simp [hy]
    · intro x hx hxy
      simp [Ne.symm hxy]
    · exact fun h => (h hy).elim
  · rw [Finset.sum_eq_zero]
    · simp [hy]
    · intro x hx
      have hxy : y ≠ x := fun h => hy (h ▸ hx)
      simp [hxy]

/-- The actual finite phase interpolation has norm at most one on the WHOLE real line. -/
theorem originalFiniteIsolationC0_norm_le_one (S : LocallyFiniteCarrier) (E : Finset S.subtype)
    (a : S.subtype → ℂ) (ha : ∀ x ∈ E, ‖a x‖ ≤ 1) : ‖originalFiniteIsolationC0 S E a‖ ≤ 1 := by
  classical
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
  intro z
  change ‖originalFiniteIsolationC0 S E a z‖ ≤ 1
  simp only [originalFiniteIsolationC0, originalC0_sum_apply,
    ZeroAtInftyContinuousMap.smul_apply, originalIsolationC0_apply, smul_eq_mul]
  by_cases h : ∃ x ∈ E, S.isolationSchwartz x z ≠ 0
  · obtain ⟨x, hx, hxn⟩ := h
    rw [Finset.sum_eq_single x]
    · rw [norm_mul]
      exact (mul_le_mul (ha x hx) (originalIsolationSchwartz_norm_le_one S x z)
        (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    · intro y hy hyx
      have hz : S.isolationSchwartz y z = 0 := by
        by_contra hyn
        exact hyx (originalIsolationSchwartz_unique_nonzero S z y x hyn hxn)
      rw [hz, mul_zero]
    · exact fun hh => (hh hx).elim
  · have hz : ∀ x ∈ E, S.isolationSchwartz x z = 0 := by
      intro x hx
      by_contra hxn
      exact h ⟨x, hx, hxn⟩
    rw [Finset.sum_eq_zero]
    · norm_num
    · intro x hx
      rw [hz x hx, mul_zero]

/-- The literal coefficient phase used to test its absolute original mass. -/
def originalCoefficientPhase (c : ℂ) : ℂ := star c / (‖c‖ : ℂ)

/-- Every literal coefficient phase has norm at most one, INCLUDING zero. -/
theorem originalCoefficientPhase_norm_le_one (c : ℂ) : ‖originalCoefficientPhase c‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [originalCoefficientPhase, hc]
  · have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    simp only [originalCoefficientPhase, norm_div, norm_star, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg c), div_self hn, le_refl]

/-- Multiplying by the actual phase gives EXACTLY the real absolute mass. -/
theorem originalCoefficientPhase_mul (c : ℂ) : c * originalCoefficientPhase c = (‖c‖ : ℂ) := by
  by_cases hc : c = 0
  · simp [originalCoefficientPhase, hc]
  · have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hc)
    unfold originalCoefficientPhase
    rw [← mul_div_assoc, Complex.star_def, Complex.mul_conj]
    rw [Complex.normSq_eq_norm_sq]
    push_cast
    field_simp

end
end MeyerGeneralProblem
