module

public import MeyerGeneralProblem.Cardinal.Strong.RationalQuarticDilation
public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalRootSearch

@[expose] public section

/-! Actual ordinary rational computation of the physical scaled original roots. -/

namespace MeyerGeneralProblem.StrongParity

/-- The executable integer error coefficient for a physical root label. -/
def scaledOriginalRootErrorCoefficient (m : ℕ) (n : ℤ) : ℕ :=
  m * (2 + originalRootSearchRadius n)

/-- The actual scaled root computation at a common internal precision. -/
def rationalScaledOriginalRootRaw (m : ℕ) (n : ℤ) (a : ℚ) (p : ℕ) : ℚ :=
  rationalDilationApprox p * m * rationalOriginalRootApprox a n p

/-- A definite precision offset gives the actual physical root at binary precision. -/
def rationalScaledOriginalRootApprox (m : ℕ) (n : ℤ) (a : ℚ) (p : ℕ) : ℚ :=
  rationalScaledOriginalRootRaw m n a (p + scaledOriginalRootErrorCoefficient m n)

noncomputable section

/-- A natural integer coefficient is paid by its explicit binary precision offset. -/
theorem nat_coefficient_binary_error (M p : ℕ) :
    (M : ℝ) * (1 / (2 : ℝ) ^ (p + M)) ≤ 1 / (2 : ℝ) ^ p := by
  have hM : (M : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast (Nat.le_succ M).trans (two_pow_ge_add_one M)
  calc
    _ ≤ (2 : ℝ) ^ M * (1 / (2 : ℝ) ^ (p + M)) := by gcongr
    _ = _ := by rw [pow_add]; field_simp

/-- Every actual compact original root is bounded by its computed integer radius. -/
theorem compactOriginalRootLabel_abs_le_radius (n : ℤ) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |compactOriginalRootLabel n a| ≤ originalRootSearchRadius n := by
  rw [compactOriginalRootLabel_eq n ha.1 ha.2]
  exact abs_le.mpr (sheetRootLabel_search_radius a ha.1 (by linarith [ha.2]) n)

/-- The actual rational input root evaluator agrees with the compact-domain semantics. -/
theorem rationalOriginalRootApprox_compact_error {a : ℚ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (n : ℤ) (p : ℕ) :
    |(rationalOriginalRootApprox a n p : ℝ) - compactOriginalRootLabel n a| ≤
      1 / (2 : ℝ) ^ p := by
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha2R : (a : ℝ) ≤ 1 / 2 := by
    have h : (a : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast ha2
    norm_num at h
    exact h
  rw [compactOriginalRootLabel_eq n haR ha2R]
  exact rationalOriginalRootApprox_error ha ha2 n p

/-- Actual scale and root errors give the explicit uniform integer coefficient. -/
theorem rationalScaledOriginalRootRaw_error (m : ℕ) (n : ℤ) {a : ℚ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (p : ℕ) :
    |(rationalScaledOriginalRootRaw m n a p : ℝ) - scaledCompactOriginalRoot m n a| ≤
      (scaledOriginalRootErrorCoefficient m n : ℝ) * (1 / (2 : ℝ) ^ p) := by
  let c := (rationalDilationApprox p : ℝ)
  let r := compactOriginalRootLabel n (a : ℝ)
  let rh := (rationalOriginalRootApprox a n p : ℝ)
  have hcr : 1 ≤ c ∧ c ≤ 2 := by
    dsimp [c]
    constructor
    · exact_mod_cast (rationalDilationApprox_range p).1
    · exact_mod_cast (rationalDilationApprox_range p).2
  have hm : (0 : ℝ) ≤ m := by positivity
  have hc : |c - parityDilationUnit| ≤ 1 / (2 : ℝ) ^ p := rationalDilationApprox_error p
  have hr : |rh - r| ≤ 1 / (2 : ℝ) ^ p := rationalOriginalRootApprox_compact_error ha ha2 n p
  have ha2R : (a : ℝ) ≤ 1 / 2 := by
    have h : (a : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast ha2
    norm_num at h
    exact h
  have hrr : |r| ≤ (originalRootSearchRadius n : ℝ) :=
    compactOriginalRootLabel_abs_le_radius n ⟨by exact_mod_cast ha, ha2R⟩
  have he : (rationalScaledOriginalRootRaw m n a p : ℝ) - scaledCompactOriginalRoot m n a =
      c * (m : ℝ) * (rh - r) + (c - parityDilationUnit) * (m : ℝ) * r := by
    simp only [rationalScaledOriginalRootRaw, Rat.cast_mul, Rat.cast_natCast,
      scaledCompactOriginalRoot]
    dsimp [c, r, rh]
    ring
  rw [he]
  calc
    _ ≤ |c * (m : ℝ) * (rh - r)| + |(c - parityDilationUnit) * (m : ℝ) * r| := abs_add_le _ _
    _ = c * (m : ℝ) * |rh - r| + |c - parityDilationUnit| * (m : ℝ) * |r| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ c),
        abs_of_nonneg hm]
    _ ≤ (2 * (m : ℝ)) * (1 / (2 : ℝ) ^ p) +
        (1 / (2 : ℝ) ^ p) * (m : ℝ) * (originalRootSearchRadius n : ℝ) := by
          gcongr
          exact hcr.2
    _ = _ := by simp only [scaledOriginalRootErrorCoefficient, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat]; ring

/-- EVERY physical scaled original root is actually computed with binary error. -/
theorem rationalScaledOriginalRootApprox_error (m : ℕ) (n : ℤ) {a : ℚ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (p : ℕ) :
    |(rationalScaledOriginalRootApprox m n a p : ℝ) - scaledCompactOriginalRoot m n a| ≤
      1 / (2 : ℝ) ^ p :=
  (rationalScaledOriginalRootRaw_error m n ha ha2 _).trans
    (nat_coefficient_binary_error (scaledOriginalRootErrorCoefficient m n) p)

end

end MeyerGeneralProblem.StrongParity
