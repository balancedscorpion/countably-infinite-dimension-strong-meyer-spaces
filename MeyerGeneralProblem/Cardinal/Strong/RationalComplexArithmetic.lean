module

public import MeyerGeneralProblem.Cardinal.Strong.RationalQuarterCoefficients

@[expose] public section

/-! Ordinary rational-coordinate arithmetic for the finite original basis algorithm. -/

namespace MeyerGeneralProblem.StrongParity

/-- Ordinary exact addition on rational complex coordinates. -/
def rationalComplexAdd (a b : ℚ × ℚ) : ℚ × ℚ := (a.1 + b.1, a.2 + b.2)

/-- Ordinary exact subtraction on rational complex coordinates. -/
def rationalComplexSub (a b : ℚ × ℚ) : ℚ × ℚ := (a.1 - b.1, a.2 - b.2)

/-- Ordinary exact multiplication on rational complex coordinates. -/
def rationalComplexMul (a b : ℚ × ℚ) : ℚ × ℚ :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- Ordinary complete finite sum on rational complex coordinates. -/
def rationalComplexSum {ι : Type*} (A : Finset ι) (f : ι → ℚ × ℚ) : ℚ × ℚ :=
  (∑ i ∈ A, (f i).1, ∑ i ∈ A, (f i).2)

/-- Ordinary complete finite dot product on rational complex coordinates. -/
def rationalComplexDot {ι : Type*} [Fintype ι] (a b : ι → ℚ × ℚ) : ℚ × ℚ :=
  rationalComplexSum Finset.univ (fun i => rationalComplexMul (a i) (b i))

/-- The literal finite degree elimination, with exact original pivot inverses. -/
def rationalComplexDegreeElimination {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (row : I → J → ℚ × ℚ)
    (inverse : I → ℚ × ℚ) (pivot : I → J) (degree : I → ℕ) :
    ℕ → (J → ℚ × ℚ) → J → ℚ × ℚ
  | 0, v => v
  | t + 1, v =>
    let w := rationalComplexDegreeElimination row inverse pivot degree t v
    fun j => rationalComplexSub (w j)
      (rationalComplexSum (Finset.univ.filter (fun i => degree i = t ∧ pivot i = j))
        (fun i => rationalComplexMul (rationalComplexDot (row i) w) (inverse i)))

noncomputable section

/-- Rational-coordinate addition has its exact complex value. -/
theorem rationalComplexAdd_value (a b : ℚ × ℚ) :
    rationalComplexValue (rationalComplexAdd a b) = rationalComplexValue a + rationalComplexValue b := by
  simp only [rationalComplexAdd, rationalComplexValue, Rat.cast_add]
  ring

/-- Rational-coordinate subtraction has its exact complex value. -/
theorem rationalComplexSub_value (a b : ℚ × ℚ) :
    rationalComplexValue (rationalComplexSub a b) = rationalComplexValue a - rationalComplexValue b := by
  simp only [rationalComplexSub, rationalComplexValue, Rat.cast_sub]
  ring

/-- Rational-coordinate multiplication has its exact complex value. -/
theorem rationalComplexMul_value (a b : ℚ × ℚ) :
    rationalComplexValue (rationalComplexMul a b) = rationalComplexValue a * rationalComplexValue b := by
  simp only [rationalComplexMul, rationalComplexValue, Rat.cast_sub, Rat.cast_add, Rat.cast_mul]
  have h := Complex.I_sq
  linear_combination -(a.2 : ℂ) * (b.2 : ℂ) * h

/-- The complete rational sum has its exact complex value. -/
theorem rationalComplexSum_value {ι : Type*} (A : Finset ι) (f : ι → ℚ × ℚ) :
    rationalComplexValue (rationalComplexSum A f) = ∑ i ∈ A, rationalComplexValue (f i) := by
  simp [rationalComplexSum, rationalComplexValue, Finset.sum_add_distrib, Finset.sum_mul]

/-- The complete rational dot product has its exact complex value. -/
theorem rationalComplexDot_value {ι : Type*} [Fintype ι] (a b : ι → ℚ × ℚ) :
    rationalComplexValue (rationalComplexDot a b) =
      ∑ i : ι, rationalComplexValue (a i) * rationalComplexValue (b i) := by
  simp [rationalComplexDot, rationalComplexSum_value, rationalComplexMul_value]

end

end MeyerGeneralProblem.StrongParity
