module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalGlobalInvariance

@[expose] public section

/-! Literal top-corner normalization and full-box coefficient products.
Every coefficient, collision and original quarter-phase factor is retained. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Multiplication by a literal original constant scales EVERY coefficient. -/
theorem originalPositive_constant_mul_coeff (q : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (c : ℂ) (n : ℕ × ℕ) :
    (q * AddMonoidAlgebra.single (0, 0) c).coeff n = q.coeff n * c := by
  change (q * AddMonoidAlgebra.single (0 : ℕ × ℕ) c).coeff n = _
  exact AddMonoidAlgebra.coeff_mul_single_zero q c n

/-- Constant multiplication preserves the SAME original square. -/
theorem originalPositive_constant_mul_inSquare (q : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (d : ℕ) (c : ℂ) (hq : OriginalPositiveInSquare q d) :
    OriginalPositiveInSquare (q * AddMonoidAlgebra.single (0, 0) c) d := by
  simpa only [Nat.add_zero] using originalPositiveInSquare_mul q _ d 0 hq
    (originalPositiveInSquare_single 0 (0, 0) c ⟨le_rfl, le_rfl⟩)

/-- Unit-character actions fix literal constants, internally. -/
theorem originalPositiveCharacterTwist_constant
    (χ : Multiplicative (ℤ × ℤ) →* ℂˣ) (c : ℂ) :
    originalPositiveCharacterTwist χ (AddMonoidAlgebra.single (0, 0) c) =
      AddMonoidAlgebra.single (0, 0) c := by
  rw [originalPositiveCharacterTwist_single]
  change AddMonoidAlgebra.single (0, 0) ((χ 1 : ℂ) * c) = _
  rw [map_one, Units.val_one, one_mul]

/-- The FULL top-corner coefficient of a bounded product is the product of
the two literal top coefficients, derived from fixed-degree chart reflection. -/
theorem originalPositive_product_top_coeff (p q : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (d e : ℕ) (hp : OriginalPositiveInSquare p d) (hq : OriginalPositiveInSquare q e) :
    (p * q).coeff (d + e, d + e) = p.coeff (d, d) * q.coeff (e, e) := by
  rw [← originalPositiveChartReflection_top_coefficient (d + e) (p * q)
    (originalPositiveInSquare_mul p q d e hp hq),
    ← originalPositiveTorusEvaluation_origin,
    originalPositiveChartReflection_mul (true, true) d e p q hp hq, map_mul,
    originalPositiveTorusEvaluation_origin, originalPositiveTorusEvaluation_origin,
    originalPositiveChartReflection_top_coefficient d p hp,
    originalPositiveChartReflection_top_coefficient e q hq]

/-- The full top coefficient of ANY finite bounded native product, including
the empty product, is computed without a nonzero-corner assumption. -/
theorem originalPositive_prod_top_coeff {ι : Type*} (s : Finset ι)
    (p : ι → AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ι → ℕ)
    (hp : ∀ i ∈ s, OriginalPositiveInSquare (p i) (d i)) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, d i, ∑ i ∈ s, d i) =
      ∏ i ∈ s, (p i).coeff (d i, d i) := by
  rw [← originalPositiveChartReflection_top_coefficient _ _ (originalPositiveInSquare_prod s p d hp),
    ← originalPositiveTorusEvaluation_origin, originalPositiveChartReflection_prod (true, true) s p d hp,
    map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [originalPositiveTorusEvaluation_origin, originalPositiveChartReflection_top_coefficient _ _ (hp i hi)]

/-- Remove exactly the actual top-corner multiple of the full divisor. -/
def originalPositiveRemoveTop (d : ℕ) (q u : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  u - q * AddMonoidAlgebra.single (0, 0) (u.coeff (d, d) / q.coeff (d, d))

/-- Top-corner normalization keeps the entire original square. -/
theorem originalPositiveRemoveTop_inSquare (d : ℕ) (q u : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hq : OriginalPositiveInSquare q d) (hu : OriginalPositiveInSquare u d) :
    OriginalPositiveInSquare (originalPositiveRemoveTop d q u) d :=
  originalPositiveInSquare_sub _ _ d hu (originalPositive_constant_mul_inSquare q d _ hq)

/-- The actual nonzero divisor top coefficient makes the normalized top zero. -/
theorem originalPositiveRemoveTop_top_zero (d : ℕ) (q u : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hd : q.coeff (d, d) ≠ 0) : (originalPositiveRemoveTop d q u).coeff (d, d) = 0 := by
  simp only [originalPositiveRemoveTop, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    originalPositive_constant_mul_coeff]
  field_simp [hd]
  ring

/-- Every previously proved private invariance survives exact normalization. -/
theorem originalPositiveRemoveTop_character_invariant (d : ℕ)
    (q u : AddMonoidAlgebra ℂ (ℕ × ℕ)) (χ : Multiplicative (ℤ × ℤ) →* ℂˣ)
    (hq : originalPositiveCharacterTwist χ q = q)
    (hu : originalPositiveCharacterTwist χ u = u) :
    originalPositiveCharacterTwist χ (originalPositiveRemoveTop d q u) = originalPositiveRemoveTop d q u := by
  rw [originalPositiveRemoveTop, map_sub, map_mul, hu, hq, originalPositiveCharacterTwist_constant]

/-- Normalization changes ONLY a literal constant between the two rational
summands and preserves the exact original numerator identity. -/
theorem originalPositiveRemoveTop_split (d : ℕ) (q e r u v : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hr : r = e * u + q * v) :
    r = e * originalPositiveRemoveTop d q u +
      q * (v + e * AddMonoidAlgebra.single (0, 0) (u.coeff (d, d) / q.coeff (d, d))) := by
  rw [hr, originalPositiveRemoveTop]
  ring

end
end MeyerGeneralProblem.StrongParity
