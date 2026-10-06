module

public import MeyerGeneralProblem.Cardinal.Strong.RationalScaledOriginalRoot
public import MeyerGeneralProblem.Cardinal.Strong.RationalNamedRootSearch

@[expose] public section

/-! Ordinary physical original root computation from an actual binary parameter name. -/

namespace MeyerGeneralProblem.StrongParity

/-- The actual scaled named-root program at a common internal precision. -/
def rationalNamedScaledOriginalRootRaw (name : ℕ → ℚ) (m : ℕ) (n : ℤ) (p : ℕ) : ℚ :=
  rationalDilationApprox p * m * rationalNamedOriginalRootApprox name n p

/-- The actual named physical original root program at the requested binary precision. -/
def rationalNamedScaledOriginalRootApprox (name : ℕ → ℚ) (m : ℕ) (n : ℤ) (p : ℕ) : ℚ :=
  rationalNamedScaledOriginalRootRaw name m n (p + scaledOriginalRootErrorCoefficient m n)

noncomputable section

/-- Actual scale and root errors give the explicit uniform integer coefficient. -/
theorem rationalNamedScaledOriginalRootRaw_error (m : ℕ) (n : ℤ) (name : ℕ → ℚ) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hname_range : ∀ p, 0 ≤ name p ∧ name p ≤ 1 / 2)
    (hname_error : ∀ p, |(name p : ℝ) - a| ≤ 1 / (2 : ℝ) ^ p) (p : ℕ) :
    |(rationalNamedScaledOriginalRootRaw name m n p : ℝ) - scaledCompactOriginalRoot m n a| ≤
      (scaledOriginalRootErrorCoefficient m n : ℝ) * (1 / (2 : ℝ) ^ p) := by
  let c := (rationalDilationApprox p : ℝ)
  let r := compactOriginalRootLabel n a
  let rh := (rationalNamedOriginalRootApprox name n p : ℝ)
  have hcr : 1 ≤ c ∧ c ≤ 2 := by
    dsimp [c]
    constructor
    · exact_mod_cast (rationalDilationApprox_range p).1
    · exact_mod_cast (rationalDilationApprox_range p).2
  have hm : (0 : ℝ) ≤ m := by positivity
  have hc : |c - parityDilationUnit| ≤ 1 / (2 : ℝ) ^ p := rationalDilationApprox_error p
  have hr : |rh - r| ≤ 1 / (2 : ℝ) ^ p := by
    dsimp [rh, r]
    rw [compactOriginalRootLabel_eq n ha.1 ha.2]
    exact rationalNamedOriginalRootApprox_error name ha.1 ha.2 hname_range hname_error n p
  have hrr : |r| ≤ (originalRootSearchRadius n : ℝ) :=
    compactOriginalRootLabel_abs_le_radius n ha
  have he : (rationalNamedScaledOriginalRootRaw name m n p : ℝ) - scaledCompactOriginalRoot m n a =
      c * (m : ℝ) * (rh - r) + (c - parityDilationUnit) * (m : ℝ) * r := by
    simp only [rationalNamedScaledOriginalRootRaw, Rat.cast_mul, Rat.cast_natCast,
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

/-- Every actual named physical original root is computed with the requested binary error. -/
theorem rationalNamedScaledOriginalRootApprox_error (name : ℕ → ℚ) (m : ℕ) (n : ℤ) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hname_range : ∀ p, 0 ≤ name p ∧ name p ≤ 1 / 2)
    (hname_error : ∀ p, |(name p : ℝ) - a| ≤ 1 / (2 : ℝ) ^ p) (p : ℕ) :
    |(rationalNamedScaledOriginalRootApprox name m n p : ℝ) - scaledCompactOriginalRoot m n a| ≤
      1 / (2 : ℝ) ^ p :=
  (rationalNamedScaledOriginalRootRaw_error m n name ha hname_range hname_error _).trans
    (nat_coefficient_binary_error (scaledOriginalRootErrorCoefficient m n) p)

end

end MeyerGeneralProblem.StrongParity
