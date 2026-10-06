module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalPositiveOrbitPartition

@[expose] public section

/-! Genuine separate-pole polynomial lifts from an exact orbit partition and
proved character-difference divisibility. The actual complete pair supplies
both inputs internally downstream; global chart compatibility is not assumed. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Finite polynomial orbit partition and literal complementary divisibility
construct the two genuine polynomial numerators, without disjoint-divisor or
multivariate Bezout assumptions on the two original denominator factors. -/
theorem originalPositiveLocalSplit_of_partition {ι : Type*} (s : Finset ι)
    (w q t : ι → AddMonoidAlgebra ℂ (ℕ × ℕ)) (Q E R : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hpart : ∑ g ∈ s, w g * q g = 1)
    (hdiv : ∀ g, E ∣ t g * Q - R * q g) :
    ∃ U V : AddMonoidAlgebra ℂ (ℕ × ℕ), R = E * U + Q * V := by
  classical
  choose b hb using hdiv
  let U := -(∑ g ∈ s, w g * b g)
  let V := ∑ g ∈ s, w g * t g
  have hs : Q * (∑ g ∈ s, w g * t g) - R * (∑ g ∈ s, w g * q g) =
      E * (∑ g ∈ s, w g * b g) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro g _
    calc
      Q * (w g * t g) - R * (w g * q g) = w g * (t g * Q - R * q g) := by ring
      _ = E * (w g * b g) := by rw [hb g]; ring
  rw [hpart, mul_one] at hs
  refine ⟨U, V, ?_⟩
  dsimp only [U, V]
  linear_combination -hs

/-- Exact polynomial decomposition gives the actual two separate denominators
in the genuine fraction field, with no extra translated divisor introduced. -/
theorem originalPositiveLocalSplit_fraction (Q E R U V : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hR : R = E * U + Q * V) (hQ : Q ≠ 0) (hE : E ≠ 0) :
    let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
    f R / f (Q * E) = f U / f Q + f V / f E := by
  let f := algebraMap (AddMonoidAlgebra ℂ (ℕ × ℕ)) (FractionRing (AddMonoidAlgebra ℂ (ℕ × ℕ)))
  have hi : Function.Injective f := IsFractionRing.injective _ _
  have hQ0 := (map_ne_zero_iff f hi).mpr hQ
  have hE0 := (map_ne_zero_iff f hi).mpr hE
  change f R / f (Q * E) = f U / f Q + f V / f E
  rw [hR, map_add, map_mul, map_mul, map_mul]
  field_simp [hQ0, hE0]

end
end MeyerGeneralProblem.StrongParity
