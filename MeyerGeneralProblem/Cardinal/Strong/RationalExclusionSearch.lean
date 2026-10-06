module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalExclusion
public import MeyerGeneralProblem.Cardinal.Strong.RationalRootConvergence
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Data.Nat.Find

@[expose] public section

/-! An ordinary exact rational certificate search whose termination follows from
the actual original analytic exclusions. No final compact parameter family is assumed.
-/

namespace MeyerGeneralProblem.StrongParity

open Filter
open scoped Topology

/-- One ordinary decoded center/precision probe and its finite Boolean tests. -/
def rationalExclusionProbe (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (m : ℕ) (u v : ℚ) (k : ℕ) : Bool :=
  match (Encodable.decode k : Option (ℚ × ℕ)) with
  | none => false
  | some (q, p) => decide (u < q ∧ q < v) &&
      codes.all (fun code => code.certificate names m q p)

noncomputable section

/-- Every nonzero literal residual eventually passes the actual rational certificate test. -/
theorem ComputedRootExclusion.certificate_eventually (names : ℕ → ℕ → ℚ) (values : ℕ → ℝ)
    (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) {q : ℚ} (hq : 0 ≤ q) (hq2 : q ≤ 1 / 2) (code : ComputedRootExclusion)
    (hne : (code.semantic values).residual m q ≠ 0) :
    ∀ᶠ p in atTop, code.certificate names m q p = true := by
  have hr : Tendsto (fun p : ℕ => 1 / (2 : ℝ) ^ p) atTop (𝓝 0) := by
    simpa only [one_div_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
  have ht : Tendsto (fun p : ℕ => 2 / (2 : ℝ) ^ p) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using hr.const_mul 2
  filter_upwards [ht.eventually_lt_const (abs_pos.mpr hne)] with p hp
  apply (code.certificate_iff names m q p).mpr
  have he := code.approx_error names values hname m hq hq2 p
  have ha := abs_sub_abs_le_abs_sub ((code.semantic values).residual m q)
    (code.approx names m q p : ℝ)
  rw [abs_sub_comm] at ha
  have hp' : 2 * (1 / (2 : ℝ) ^ p) < |(code.semantic values).residual m q| := by
    simpa only [mul_one_div] using hp
  have hm : (0 : ℝ) < (code.margin names m q p : ℝ) := by
    simp only [ComputedRootExclusion.margin, Rat.cast_sub, Rat.cast_abs, rationalBinaryRadius_cast]
    linarith
  exact_mod_cast hm

/-- The implemented decoded probe tests exactly the slot and every finite residual certificate. -/
theorem rationalExclusionProbe_spec (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (m : ℕ) (u v : ℚ) {k : ℕ} (hk : rationalExclusionProbe codes names m u v k = true) :
    ∃ q : ℚ, ∃ p : ℕ, (Encodable.decode k : Option (ℚ × ℕ)) = some (q, p) ∧
      u < q ∧ q < v ∧ ∀ code ∈ codes, code.certificate names m q p = true := by
  unfold rationalExclusionProbe at hk
  cases hd : (Encodable.decode k : Option (ℚ × ℕ)) with
  | none => simp only [hd, Bool.false_eq_true] at hk
  | some pair =>
      rcases pair with ⟨q, p⟩
      simp only [hd, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hk
      exact ⟨q, p, rfl, hk.1.1, hk.1.2, hk.2⟩

/-- Actual analytic finite-center existence pays termination of the ordinary certificate search. -/
theorem rationalExclusionProbe_exists (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (values : ℕ → ℝ) (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) (hm : 0 < m) (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v) :
    ∃ k, rationalExclusionProbe codes names m u v k = true := by
  have hvR : (v : ℝ) ≤ 1 / 2 := by
    have h : (v : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hv
    norm_num at h
    exact h
  obtain ⟨q, hqu, hqv, hn⟩ := actual_finite_root_exclusions_rational_center
    (u := (u : ℝ)) (v := (v : ℝ))
    m hm (fun i : Fin codes.length => (codes.get i).semantic values)
    (by exact_mod_cast hu) hvR (by exact_mod_cast huv)
  have hquQ : u < q := by exact_mod_cast hqu
  have hqvQ : q < v := by exact_mod_cast hqv
  have hq : 0 ≤ q := (hu.trans hquQ).le
  have hq2 : q ≤ 1 / 2 := hqvQ.le.trans hv
  have hall : ∀ᶠ p in atTop, ∀ i : Fin codes.length,
      (codes.get i).certificate names m q p = true :=
    eventually_all.mpr (fun i => (codes.get i).certificate_eventually names values hname m hq hq2 (hn i))
  obtain ⟨p, hp⟩ := hall.exists
  refine ⟨Encodable.encode (q, p), ?_⟩
  simp only [rationalExclusionProbe, Encodable.encodek, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  refine ⟨⟨hquQ, hqvQ⟩, ?_⟩
  intro code hc
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hc
  exact hi ▸ hp i

end

/-- The ordinary sequential search over decoded rational centers and precisions.
The real values and validity proofs pay termination and are erased from execution. -/
def rationalExclusionSearch (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (values : ℕ → ℝ) (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) (hm : 0 < m) (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v) : ℕ :=
  Nat.find (rationalExclusionProbe_exists codes names values hname m hm u v hu hv huv)

noncomputable section

/-- The implemented ordinary search terminates at an actual successful finite certificate probe. -/
theorem rationalExclusionSearch_success (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (values : ℕ → ℝ) (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) (hm : 0 < m) (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v) :
    rationalExclusionProbe codes names m u v
      (rationalExclusionSearch codes names values hname m hm u v hu hv huv) = true :=
  Nat.find_spec (rationalExclusionProbe_exists codes names values hname m hm u v hu hv huv)

/-- The actual computed search output gives a rational center and positive literal original margins. -/
theorem rationalExclusionSearch_sound (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (values : ℕ → ℝ) (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) (hm : 0 < m) (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v) :
    ∃ q : ℚ, ∃ p : ℕ,
      (Encodable.decode (rationalExclusionSearch codes names values hname m hm u v hu hv huv) :
        Option (ℚ × ℕ)) = some (q, p) ∧ u < q ∧ q < v ∧
      ∀ code ∈ codes, 0 < code.margin names m q p ∧ (code.semantic values).residual m q ≠ 0 := by
  obtain ⟨q, p, hd, hqu, hqv, hc⟩ := rationalExclusionProbe_spec codes names m u v
    (rationalExclusionSearch_success codes names values hname m hm u v hu hv huv)
  refine ⟨q, p, hd, hqu, hqv, ?_⟩
  intro code hcode
  exact ⟨(code.certificate_iff names m q p).mp (hc code hcode),
    code.certificate_sound names values hname m (hu.trans hqu).le (hqv.le.trans hv) p (hc code hcode)⟩

end

end MeyerGeneralProblem.StrongParity
