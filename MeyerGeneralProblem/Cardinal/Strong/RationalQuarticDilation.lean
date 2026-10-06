module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalRootExclusionBounds

@[expose] public section

/-! Ordinary exact rational bisection for the actual positive quartic dilation. -/

namespace MeyerGeneralProblem.StrongParity

/-- One exact rational fourth-power comparison and interval-halving step. -/
def rationalQuarticStep (s : ℚ × ℚ) : ℚ × ℚ :=
  let mid := (s.1 + s.2) / 2
  if mid ^ 4 ≤ 2 then (mid, s.2) else (s.1, mid)

/-- A definite finite bisection of the initial interval [1,2]. -/
def rationalQuarticInterval : ℕ → ℚ × ℚ
  | 0 => (1, 2)
  | p + 1 => rationalQuarticStep (rationalQuarticInterval p)

/-- The ordinary rational lower endpoint approximating the fixed dilation c. -/
def rationalDilationApprox (p : ℕ) : ℚ := (rationalQuarticInterval p).1

noncomputable section

/-- The actual positive quartic dilation is at least one. -/
theorem parityDilationUnit_one_le : 1 ≤ parityDilationUnit := by
  dsimp [parityDilationUnit]
  exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (by norm_num))

/-- Every computed bisection interval contains the actual dilation and stays in [1,2]. -/
theorem rationalQuarticInterval_encloses (p : ℕ) :
    1 ≤ ((rationalQuarticInterval p).1 : ℝ) ∧
    ((rationalQuarticInterval p).1 : ℝ) ≤ parityDilationUnit ∧
    parityDilationUnit ≤ ((rationalQuarticInterval p).2 : ℝ) ∧
    ((rationalQuarticInterval p).2 : ℝ) ≤ 2 := by
  induction p with
  | zero =>
      simp only [rationalQuarticInterval, Rat.cast_one, Rat.cast_ofNat]
      exact ⟨le_rfl, parityDilationUnit_one_le, parityDilationUnit_le_two, le_rfl⟩
  | succ p ih =>
      let s := rationalQuarticInterval p
      let mid : ℚ := (s.1 + s.2) / 2
      have hlo : 1 ≤ (s.1 : ℝ) := ih.1
      have hlc : (s.1 : ℝ) ≤ parityDilationUnit := ih.2.1
      have hch : parityDilationUnit ≤ (s.2 : ℝ) := ih.2.2.1
      have hhi : (s.2 : ℝ) ≤ 2 := ih.2.2.2
      have hmid : (mid : ℝ) = ((s.1 : ℝ) + (s.2 : ℝ)) / 2 := by
        simp [mid]
      have hml : 1 ≤ (mid : ℝ) := by linarith
      have hmh : (mid : ℝ) ≤ 2 := by linarith
      change 1 ≤ ((rationalQuarticStep s).1 : ℝ) ∧
        ((rationalQuarticStep s).1 : ℝ) ≤ parityDilationUnit ∧
        parityDilationUnit ≤ ((rationalQuarticStep s).2 : ℝ) ∧
        ((rationalQuarticStep s).2 : ℝ) ≤ 2
      by_cases ht : mid ^ 4 ≤ 2
      · have htR : (mid : ℝ) ^ 4 ≤ 2 := by exact_mod_cast ht
        have hmc : (mid : ℝ) ≤ parityDilationUnit := by
          apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) parityDilationUnit_pos.le
          simpa only [parityDilationUnit_fourth] using htR
        have hstep : rationalQuarticStep s = (mid, s.2) := ite_eq_left ht
        rw [hstep]
        exact ⟨hml, hmc, hch, hhi⟩
      · have htR : 2 < (mid : ℝ) ^ 4 := by exact_mod_cast (lt_of_not_ge ht)
        have hcm : parityDilationUnit ≤ (mid : ℝ) := by
          apply (lt_of_pow_lt_pow_left₀ 4 (by linarith : (0 : ℝ) ≤ mid) _).le
          simpa only [parityDilationUnit_fourth] using htR
        have hstep : rationalQuarticStep s = (s.1, mid) := ite_eq_right ht
        rw [hstep]
        exact ⟨hlo, hlc, hcm, hmh⟩

/-- The definite program halves the rational width at every step. -/
theorem rationalQuarticInterval_width (p : ℕ) :
    (rationalQuarticInterval p).2 - (rationalQuarticInterval p).1 = 1 / (2 : ℚ) ^ p := by
  induction p with
  | zero => norm_num [rationalQuarticInterval]
  | succ p ih =>
      have hs : (rationalQuarticStep (rationalQuarticInterval p)).2 -
          (rationalQuarticStep (rationalQuarticInterval p)).1 =
          ((rationalQuarticInterval p).2 - (rationalQuarticInterval p).1) / 2 := by
        dsimp [rationalQuarticStep]
        split_ifs <;> dsimp <;> ring
      rw [rationalQuarticInterval, hs, ih, pow_succ]
      ring

/-- Every emitted approximation has a safe positive denominator for reciprocal use. -/
theorem rationalDilationApprox_range (p : ℕ) :
    1 ≤ rationalDilationApprox p ∧ rationalDilationApprox p ≤ 2 := by
  have h := rationalQuarticInterval_encloses p
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2.1.trans parityDilationUnit_le_two

/-- The implemented ordinary finite quartic program has the requested binary error. -/
theorem rationalDilationApprox_error (p : ℕ) :
    |(rationalDilationApprox p : ℝ) - parityDilationUnit| ≤ 1 / (2 : ℝ) ^ p := by
  have he := rationalQuarticInterval_encloses p
  have hw : ((rationalQuarticInterval p).2 : ℝ) -
      ((rationalQuarticInterval p).1 : ℝ) = 1 / (2 : ℝ) ^ p := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (rationalQuarticInterval_width p)
    push_cast at h
    exact h
  rw [rationalDilationApprox, abs_of_nonpos (sub_nonpos.mpr he.2.1)]
  linarith [he.2.2.1]

end

end MeyerGeneralProblem.StrongParity
