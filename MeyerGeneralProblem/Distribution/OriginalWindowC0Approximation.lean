module

public import MeyerGeneralProblem.Distribution.OriginalWeightedDualWindowConstraints

@[expose] public section

/-! Actual smooth compact cutoffs approximate EVERY full C0 test in norm.
The cutoff has inner radius n+1 and outer radius 2(n+1); no approximation,
uniform tail or limiting support certificate is assumed. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty ContDiff

/-- A cofinal explicit increasing sequence of positive real window radii. -/
def originalWindowRadius (n : ℕ) : ℝ := 2 * ((n : ℝ) + 1)

/-- Actual smooth bump with the stated inner and outer radii. -/
def originalWindowBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (n : ℝ) + 1
  rOut := originalWindowRadius n
  rIn_pos := by positivity
  rIn_lt_rOut := by unfold originalWindowRadius; linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The actual complex compact smooth cutoff, as a FULL Schwartz test. -/
def originalWindowSchwartz (n : ℕ) : SchwartzMap ℝ ℂ := by
  let b := originalWindowBump n
  let f : ℝ → ℂ := Complex.ofRealCLM ∘ b
  have hs : HasCompactSupport f := b.hasCompactSupport.comp_left rfl
  have hd : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp b.contDiff
  exact hs.toSchwartzMap hd

/-- The same cutoff in the genuine C0 predual. -/
def originalWindowC0Cutoff (n : ℕ) : C₀(ℝ, ℂ) := (originalWindowSchwartz n).toZeroAtInfty

/-- EVERY real cutoff value is the actual real smooth bump. -/
theorem originalWindowC0Cutoff_apply (n : ℕ) (x : ℝ) :
    originalWindowC0Cutoff n x = (originalWindowBump n x : ℝ) := rfl

/-- The actual cutoff equals one throughout its growing inner closed window. -/
theorem originalWindowC0Cutoff_one (n : ℕ) (x : ℝ) (hx : |x| ≤ (n : ℝ) + 1) :
    originalWindowC0Cutoff n x = 1 := by
  rw [originalWindowC0Cutoff_apply, (originalWindowBump n).one_of_mem_closedBall]
  · norm_num
  · simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, originalWindowBump] using hx

/-- The actual cutoff vanishes on the FULL closed exterior at its outer radius. -/
theorem originalWindowC0Cutoff_zero (n : ℕ) (x : ℝ) (hx : originalWindowRadius n ≤ |x|) :
    originalWindowC0Cutoff n x = 0 := by
  rw [originalWindowC0Cutoff_apply, (originalWindowBump n).zero_of_le_dist]
  · norm_num
  · simpa only [dist_zero_right, Real.norm_eq_abs, originalWindowBump] using hx

/-- The full C0 error is bounded internally by the actual original test tail. -/
theorem originalWindowC0Cutoff_error_le (n : ℕ) (g : C₀(ℝ, ℂ)) (ε : ℝ) (hε : 0 ≤ ε)
    (htail : ∀ x : ℝ, (n : ℝ) + 1 < |x| → ‖g x‖ ≤ ε) :
    ‖originalWindowC0Cutoff n * g - g‖ ≤ ε := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le hε).mpr
  intro x
  change ‖originalWindowC0Cutoff n x * g x - g x‖ ≤ ε
  by_cases hx : |x| ≤ (n : ℝ) + 1
  · rw [originalWindowC0Cutoff_one n x hx, one_mul, sub_self, norm_zero]
    exact hε
  · rw [originalWindowC0Cutoff_apply]
    have he : ((originalWindowBump n x : ℝ) : ℂ) * g x - g x =
        (((originalWindowBump n x : ℝ) - 1 : ℝ) : ℂ) * g x := by push_cast; ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb : |(originalWindowBump n x : ℝ) - 1| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [(originalWindowBump n).nonneg (x := x),
        (originalWindowBump n).le_one (x := x)]
    exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans
      (by simpa only [one_mul] using htail x (lt_of_not_ge hx))

/-- Multiplying EVERY full C0 test by these actual cutoffs converges in C0 norm. -/
theorem originalWindowC0Cutoff_mul_tendsto (g : C₀(ℝ, ℂ)) :
    Filter.Tendsto (fun n : ℕ => originalWindowC0Cutoff n * g) Filter.atTop (nhds g) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨r, hr⟩ := ZeroAtInftyContinuousMapClass.norm_le g (ε / 2) (half_pos hε)
  obtain ⟨k, hk⟩ := exists_nat_gt r
  refine ⟨k, ?_⟩
  intro n hn
  rw [dist_eq_norm]
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
  have herr := originalWindowC0Cutoff_error_le n g (ε / 2) (le_of_lt (half_pos hε))
    (fun x hx => (hr x (by rw [Real.norm_eq_abs]; linarith)).le)
  exact herr.trans_lt (half_lt_self hε)

/-- EVERY full C0 test vanishing on the prefix has a cutoff vanishing on
the actual prefix PLUS ALL real exterior points. -/
theorem originalWindowC0Cutoff_mul_vanishes (L : Set ℝ) (n : ℕ) (g : C₀(ℝ, ℂ))
    (hg : ∀ x ∈ L, g x = 0) :
    ∀ x ∈ originalExteriorWindow L (originalWindowRadius n),
      (originalWindowC0Cutoff n * g) x = 0 := by
  intro x hx
  rw [ZeroAtInftyContinuousMap.mul_apply]
  rcases hx with hx | hx
  · rw [hg x hx, mul_zero]
  · rw [originalWindowC0Cutoff_zero n x hx, zero_mul]

end
end MeyerGeneralProblem
