module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalChartReflection

@[expose] public section

/-! Exact native character transport on each fixed projective chart. Reversed
coordinates invert their character; the degree scalar cancels from fractions
with equally bounded numerator and denominator. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The genuine integer character after the chart's signed coordinate substitution. -/
def originalChartCharacter (c : Bool × Bool) (χ : Multiplicative (ℤ × ℤ) →* ℂˣ) :
    Multiplicative (ℤ × ℤ) →* ℂˣ where
  toFun n := χ (Multiplicative.ofAdd (originalChartIntegerSign c n.toAdd))
  map_one' := by
    change χ (Multiplicative.ofAdd (originalChartIntegerSign c 0)) = 1
    rw [map_zero]
    exact map_one χ
  map_mul' n m := by
    change χ (Multiplicative.ofAdd (originalChartIntegerSign c (n.toAdd + m.toAdd))) = _
    rw [map_add]
    exact map_mul χ _ _

/-- The signed integer character keeps the exact unit value. -/
theorem originalChartCharacter_apply (c : Bool × Bool) (χ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (n : ℤ × ℤ) : originalChartCharacter c χ (Multiplicative.ofAdd n) =
      χ (Multiplicative.ofAdd (originalChartIntegerSign c n)) := rfl

/-- Chart transport keeps pointwise character products exactly. -/
theorem originalChartCharacter_mul (c : Bool × Bool) (χ ψ : Multiplicative (ℤ × ℤ) →* ℂˣ) :
    originalChartCharacter c (χ * ψ) = originalChartCharacter c χ * originalChartCharacter c ψ := by
  ext n
  rfl

/-- Inverting the selected character coordinates twice returns the WHOLE original character. -/
theorem originalChartCharacter_involutive (c : Bool × Bool) (χ : Multiplicative (ℤ × ℤ) →* ℂˣ) :
    originalChartCharacter c (originalChartCharacter c χ) = χ := by
  apply MonoidHom.ext
  intro n
  change χ (Multiplicative.ofAdd (originalChartIntegerSign c (originalChartIntegerSign c n.toAdd))) = χ n
  rw [originalChartIntegerSign_involutive c n.toAdd]
  rfl

/-- The fixed degree scalar and signed reflected row give EXACTLY the original unit character. -/
theorem originalChartCharacter_reflected_weight (c : Bool × Bool) (d : ℕ)
    (χ : Multiplicative (ℤ × ℤ) →* ℂˣ) (n : ℤ × ℤ) :
    χ (Multiplicative.ofAdd (originalChartIntegerShift c d)) *
      originalChartCharacter c χ (Multiplicative.ofAdd (originalChartIntegerIndex c d n)) =
        χ (Multiplicative.ofAdd n) := by
  rw [originalChartCharacter_apply, ← map_mul]
  change χ (Multiplicative.ofAdd (originalChartIntegerIndex c d (originalChartIntegerIndex c d n))) = _
  rw [originalChartIntegerIndex_involutive c d n]

/-- Whole Laurent character twists commute with fixed reflection with the exact degree scalar. -/
theorem originalLaurentChartReflection_twist (c : Bool × Bool) (d : ℕ)
    (χ : Multiplicative (ℤ × ℤ) →* ℂˣ) (p : AddMonoidAlgebra ℂ (ℤ × ℤ)) :
    originalLaurentChartReflection c d (originalLaurentCharacterTwist χ p) =
      (χ (Multiplicative.ofAdd (originalChartIntegerShift c d)) : ℂ) •
        originalLaurentCharacterTwist (originalChartCharacter c χ) (originalLaurentChartReflection c d p) := by
  refine AddMonoidAlgebra.induction_linear p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq, smul_add]
  · intro n a
    rw [originalLaurentCharacterTwist_single, originalLaurentChartReflection_single,
      originalLaurentChartReflection_single, originalLaurentCharacterTwist_single]
    simp only [AddMonoidAlgebra.smul_single, smul_eq_mul]
    congr 1
    rw [← mul_assoc, ← Units.val_mul, originalChartCharacter_reflected_weight]

/-- The actual positive character reflection identity follows using the INTERNALLY proved full square. -/
theorem originalPositiveChartReflection_twist (c : Bool × Bool) (d : ℕ)
    (χ : Multiplicative (ℤ × ℤ) →* ℂˣ) (p : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hp : OriginalPositiveInSquare p d) :
    originalPositiveChartReflection c d (originalPositiveCharacterTwist χ p) =
      (χ (Multiplicative.ofAdd (originalChartIntegerShift c d)) : ℂ) •
        originalPositiveCharacterTwist (originalChartCharacter c χ) (originalPositiveChartReflection c d p) := by
  apply originalPositiveLaurentEmbedding_injective
  rw [originalPositiveChartReflection_laurent c d _ (originalPositiveInSquare_twist χ p d hp),
    originalPositiveCharacterTwist_laurent, originalLaurentChartReflection_twist, map_smul,
    originalPositiveCharacterTwist_laurent, originalPositiveChartReflection_laurent c d p hp]

/-- Positive fixed chart reflection keeps every coefficient on its exact reflected native row. -/
theorem originalPositiveChartReflection_coeff_reflected (c : Bool × Bool) (d : ℕ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : OriginalPositiveInSquare p d)
    (n : ℕ × ℕ) (hn : n.1 ≤ d ∧ n.2 ≤ d) :
    (originalPositiveChartReflection c d p).coeff (originalChartNativeIndex c d n) = p.coeff n := by
  let S : Set (ℕ × ℕ) := {m | m.1 ≤ d ∧ m.2 ≤ d}
  have hi : Set.InjOn (originalChartNativeIndex c d) S := by
    intro a ha b hb he
    have h := congrArg (originalChartNativeIndex c d) he
    rw [originalChartNativeIndex_involutive_on_square c d a ha,
      originalChartNativeIndex_involutive_on_square c d b hb] at h
    exact h
  exact Finsupp.mapDomain_apply' S p.coeff (fun m hm => hp m hm) hi hn

/-- The actual two-coordinate prime-torus action after chart inversion. -/
def originalScheduledChartPrimeTorus (c : Bool × Bool) (bound : ℕ → ℕ) (i : ℕ)
    (g : OriginalScheduledPrimeTorus bound i) : OriginalScheduledPrimeTorus bound i :=
  (if c.1 then g.1⁻¹ else g.1, if c.2 then g.2⁻¹ else g.2)

/-- Actual native prime characters are transported by inverting precisely the reversed coordinates. -/
theorem originalScheduledChartPrimeCharacter (c : Bool × Bool) (bound : ℕ → ℕ) (i : ℕ)
    (g : OriginalScheduledPrimeTorus bound i) :
    originalChartCharacter c (originalScheduledPrimeCharacter bound i g) =
      originalScheduledPrimeCharacter bound i (originalScheduledChartPrimeTorus c bound i g) := by
  apply MonoidHom.ext
  intro n
  change g.1.val ^ (if c.1 then -n.toAdd.1 else n.toAdd.1) *
    g.2.val ^ (if c.2 then -n.toAdd.2 else n.toAdd.2) =
      (if c.1 then g.1⁻¹ else g.1).val ^ n.toAdd.1 * (if c.2 then g.2⁻¹ else g.2).val ^ n.toAdd.2
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> simp [zpow_neg]

/-- ALL original prime-torus elements occur on EACH chart; inversion has no missing characters. -/
theorem originalScheduledChartPrimeTorus_involutive (c : Bool × Bool) (bound : ℕ → ℕ) (i : ℕ)
    (g : OriginalScheduledPrimeTorus bound i) :
    originalScheduledChartPrimeTorus c bound i (originalScheduledChartPrimeTorus c bound i g) = g := by
  rcases g with ⟨ζ, η⟩
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> simp [originalScheduledChartPrimeTorus] <;> rfl

end
end MeyerGeneralProblem.StrongParity
