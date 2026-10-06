module

public import MeyerGeneralProblem.Distribution.OriginalStrongEvaluation
public import Mathlib.Analysis.Normed.Group.ZeroAtInfty

@[expose] public section

/-! The ACTUAL original polynomial weight sends every full Schwartz test to
C0, continuously in the original Schwartz seminorms. The literal weight
(1+|x|)^N is retained at ALL real points, without a substitute Hilbert norm. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty

/-- The literal original weighted Schwartz value has exactly its original real norm. -/
theorem originalWeightedSchwartzValue_norm (N : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖(1 + |x|) ^ N • f x‖ = (1 + |x|) ^ N * ‖f x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- One original seminorm family bounds the actual weighted values on the ENTIRE real line. -/
theorem originalWeightedSchwartzValue_le_seminorm (N : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (1 + |x|) ^ N * ‖f x‖ ≤
      2 ^ N * (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f := by
  convert! SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl f x using 1
  norm_num [Real.norm_eq_abs, norm_iteratedFDeriv_zero, schwartzSeminormFamily]

/-- The actual weighted Schwartz values vanish at infinity, paid by one
higher ORIGINAL seminorm rather than an assumed tail bound. -/
theorem originalWeightedSchwartzValue_zero_at_infty (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    Filter.Tendsto (fun x : ℝ => (1 + |x|) ^ N • f x)
      (Filter.cocompact ℝ) (nhds 0) := by
  apply zero_at_infty_of_norm_le
  intro ε hε
  let K := 2 ^ (N + 1) * (Finset.Iic (N + 1, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f
  refine ⟨K / ε, ?_⟩
  intro x hx
  rw [Real.norm_eq_abs] at hx
  rw [originalWeightedSchwartzValue_norm]
  have h := originalWeightedSchwartzValue_le_seminorm (N + 1) f x
  change (1 + |x|) ^ (N + 1) * ‖f x‖ ≤ K at h
  rw [pow_succ] at h
  have hk : K < |x| * ε := (div_lt_iff₀ hε).mp hx
  have hw : 0 < 1 + |x| := by positivity
  nlinarith

/-- EVERY full Schwartz test with its ACTUAL original polynomial weight, as C0. -/
def originalWeightedSchwartzC0 (N : ℕ) (f : SchwartzMap ℝ ℂ) : C₀(ℝ, ℂ) where
  toFun x := (1 + |x|) ^ N • f x
  continuous_toFun := ((continuous_const.add continuous_abs).pow N).smul f.continuous
  zero_at_infty' := originalWeightedSchwartzValue_zero_at_infty N f

/-- ALL-point formula of the actual weighted C0 test. -/
theorem originalWeightedSchwartzC0_apply (N : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    originalWeightedSchwartzC0 N f x = (1 + |x|) ^ N • f x := rfl

/-- The C0 norm of the actual weighted test is bounded by the original Schwartz seminorm. -/
theorem originalWeightedSchwartzC0_norm_le (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖originalWeightedSchwartzC0 N f‖ ≤
      2 ^ N * (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change ‖(1 + |x|) ^ N • f x‖ ≤ _
  rw [originalWeightedSchwartzValue_norm]
  exact originalWeightedSchwartzValue_le_seminorm N f x

/-- The ACTUAL original weighted Schwartz-to-C0 operator is complex continuous linear. -/
def originalWeightedSchwartzC0CLM (N : ℕ) : SchwartzMap ℝ ℂ →L[ℂ] C₀(ℝ, ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (originalWeightedSchwartzC0 N)
    (by intro f g; ext x; simp [originalWeightedSchwartzC0_apply, smul_add])
    (by intro a f; ext x; simp [originalWeightedSchwartzC0_apply]; ring)
    ⟨Finset.Iic (N, 0), 2 ^ N, by positivity, originalWeightedSchwartzC0_norm_le N⟩

/-- ALL real values of the genuine continuous linear operator retain the original weight. -/
theorem originalWeightedSchwartzC0CLM_apply (N : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    originalWeightedSchwartzC0CLM N f x = (1 + |x|) ^ N • f x := rfl

/-- No full Schwartz test is lost in the original weighted C0 embedding. -/
theorem originalWeightedSchwartzC0CLM_injective (N : ℕ) :
    Function.Injective (originalWeightedSchwartzC0CLM N) := by
  intro f g h
  ext x
  have he := congrArg (fun u : C₀(ℝ, ℂ) => u x) h
  change (((1 + |x|) ^ N : ℝ) : ℂ) * f x = (((1 + |x|) ^ N : ℝ) : ℂ) * g x at he
  have hw : (1 + |x|) ^ N ≠ 0 := by positivity
  exact mul_left_cancel₀ (by exact_mod_cast hw : (((1 + |x|) ^ N : ℝ) : ℂ) ≠ 0) he

end
end MeyerGeneralProblem
