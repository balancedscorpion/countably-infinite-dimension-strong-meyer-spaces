module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPoleCancellation
public import Mathlib.Algebra.MonoidAlgebra.Support

@[expose] public section

/-! Fixed native square bounds for the actual projective chart transport.
Bounds use the complete degree, never the numerator's own degree. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped Pointwise

/-- All actual positive coefficients lie in the fixed native square. -/
def OriginalPositiveInSquare (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ℕ) : Prop :=
  ∀ n ∈ p.coeff.support, n.1 ≤ d ∧ n.2 ≤ d

/-- The zero polynomial lies in every fixed square. -/
theorem originalPositiveInSquare_zero (d : ℕ) : OriginalPositiveInSquare 0 d := by
  simp [OriginalPositiveInSquare]

/-- A literal monomial has the prescribed square bound. -/
theorem originalPositiveInSquare_single (d : ℕ) (n : ℕ × ℕ) (c : ℂ)
    (hn : n.1 ≤ d ∧ n.2 ≤ d) : OriginalPositiveInSquare (AddMonoidAlgebra.single n c) d := by
  intro m hm
  have hmn : m = n := by
    exact Finset.mem_singleton.mp (Finsupp.support_single_subset hm)
  simpa [hmn] using hn

/-- Addition keeps all coefficients inside the common fixed square, including collisions. -/
theorem originalPositiveInSquare_add (p q : AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ℕ)
    (hp : OriginalPositiveInSquare p d) (hq : OriginalPositiveInSquare q d) :
    OriginalPositiveInSquare (p + q) d := by
  intro n hn
  rcases Finset.mem_union.mp (Finsupp.support_add hn) with h | h
  · exact hp n h
  · exact hq n h

/-- Negation keeps the exact same fixed square. -/
theorem originalPositiveInSquare_neg (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ℕ)
    (hp : OriginalPositiveInSquare p d) : OriginalPositiveInSquare (-p) d := by
  intro n hn
  exact hp n (by simpa using hn)

/-- Subtraction keeps every original coefficient collision within the fixed square. -/
theorem originalPositiveInSquare_sub (p q : AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ℕ)
    (hp : OriginalPositiveInSquare p d) (hq : OriginalPositiveInSquare q d) :
    OriginalPositiveInSquare (p - q) d := by
  simpa only [sub_eq_add_neg] using originalPositiveInSquare_add p (-q) d hp
    (originalPositiveInSquare_neg q d hq)

/-- Multiplication adds fixed square bounds, without discarding coefficient collisions. -/
theorem originalPositiveInSquare_mul (p q : AddMonoidAlgebra ℂ (ℕ × ℕ)) (d e : ℕ)
    (hp : OriginalPositiveInSquare p d) (hq : OriginalPositiveInSquare q e) :
    OriginalPositiveInSquare (p * q) (d + e) := by
  classical
  intro n hn
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset p q hn)
  exact ⟨Nat.add_le_add (hp a ha).1 (hq b hb).1, Nat.add_le_add (hp a ha).2 (hq b hb).2⟩

/-- The retained collision-aware product theorem supplies every fixed product square. -/
theorem originalPositiveInSquare_prod {ι : Type*} (s : Finset ι)
    (p : ι → AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ι → ℕ)
    (hp : ∀ i ∈ s, OriginalPositiveInSquare (p i) (d i)) :
    OriginalPositiveInSquare (∏ i ∈ s, p i) (∑ i ∈ s, d i) := by
  intro n hn
  exact finiteOriginalPositivePolynomialProduct_support_box s p d hp hn

/-- Genuine unit characters keep the actual coefficient square. -/
theorem originalPositiveInSquare_twist (χ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ℕ) (hp : OriginalPositiveInSquare p d) :
    OriginalPositiveInSquare (originalPositiveCharacterTwist χ p) d := by
  intro n hn
  have h := Finsupp.mem_support_iff.mp hn
  rw [originalPositiveCharacterTwist_coefficient] at h
  exact hp n (Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp h).2)

/-- EVERY literal phased sheet has its fixed native square, even at coefficient degeneracies. -/
theorem originalPhasedPositiveSheetPolynomial_inSquare (d : ℕ) (a : ℝ) (ρ σ : ℂ) :
    OriginalPositiveInSquare (originalPhasedPositiveSheetPolynomial d a ρ σ) d := by
  classical
  intro n hn
  by_cases h0 : n = (0, 0)
  · subst n; simp
  by_cases h1 : n = (0, d)
  · subst n; simp
  by_cases h2 : n = (d, 0)
  · subst n; simp
  by_cases h3 : n = (d, d)
  · subst n; simp
  exact False.elim ((Finsupp.mem_support_iff.mp hn)
    (by simp [originalPhasedPositiveSheetPolynomial, h0, h1, h2, h3]))

/-- The actual complete denominator's retained full square is supplied internally. -/
theorem originalScheduledPrefixPolynomial_inSquare (bound : ℕ → ℕ) (k : ℕ) :
    OriginalPositiveInSquare (originalScheduledPrefixPolynomial bound k)
      (originalScheduledPrefixPolynomialDegree bound k) := by
  exact fun _ hn => originalScheduledPrefixPolynomial_support_box bound k hn

/-- EVERY actual complete pair supplies its entire numerator square internally. -/
theorem originalScheduledPrefixPositiveNumerator_inSquare (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k)) :
    OriginalPositiveInSquare (originalScheduledPrefixPositiveNumerator bound k T hT)
      (originalScheduledPrefixPolynomialDegree bound k) := by
  intro n hn
  have h := originalScheduledPrefixPositiveNumerator_support_box bound k T hT hn
  exact ⟨h.1, h.2.1⟩

end
end MeyerGeneralProblem.StrongParity
