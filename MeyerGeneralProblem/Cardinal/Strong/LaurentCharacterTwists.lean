module

public import MeyerGeneralProblem.Cardinal.Strong.AnnihilatorArrays
public import Mathlib.Algebra.MonoidAlgebra.Basic

@[expose] public section

/-! Genuine character automorphisms of finite Laurent coefficients and their
whole integer arrays. All operations retain coefficient collisions exactly;
there is no analytic restriction or rational-presentation assumption here. -/
namespace MeyerGeneralProblem
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- The actual character-weighted Laurent monomial homomorphism. -/
def originalLaurentCharacterMonomial (χ : Multiplicative G →* ℂˣ) :
    Multiplicative G →* AddMonoidAlgebra ℂ G where
  toFun n := AddMonoidAlgebra.single n.toAdd (χ n : ℂ)
  map_one' := by simp [AddMonoidAlgebra.one_def]
  map_mul' n m := by simp [AddMonoidAlgebra.single_mul_single]

/-- Exact algebra action of a unit-valued character on the FULL Laurent polynomial. -/
def originalLaurentCharacterTwist (χ : Multiplicative G →* ℂˣ) :
    AddMonoidAlgebra ℂ G →ₐ[ℂ] AddMonoidAlgebra ℂ G :=
  AddMonoidAlgebra.lift ℂ (AddMonoidAlgebra ℂ G) G (originalLaurentCharacterMonomial χ)

/-- Every original monomial coefficient receives exactly its character value. -/
theorem originalLaurentCharacterTwist_single (χ : Multiplicative G →* ℂˣ) (n : G) (c : ℂ) :
    originalLaurentCharacterTwist χ (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single n ((χ (Multiplicative.ofAdd n) : ℂ) * c) := by
  classical
  rw [originalLaurentCharacterTwist, AddMonoidAlgebra.lift_single]
  change c • AddMonoidAlgebra.single n (χ (Multiplicative.ofAdd n) : ℂ) = _
  ext z
  simp only [AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single, Finsupp.smul_apply,
    smul_eq_mul]
  simp only [Finsupp.single_apply]
  split_ifs <;> ring

/-- EVERY original finite coefficient is twisted exactly once, after all collisions. -/
theorem originalLaurentCharacterTwist_coefficient (χ : Multiplicative G →* ℂˣ)
    (p : AddMonoidAlgebra ℂ G) (n : G) :
    (originalLaurentCharacterTwist χ p).coeff n = (χ (Multiplicative.ofAdd n) : ℂ) * p.coeff n := by
  classical
  refine AddMonoidAlgebra.induction_linear p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]
  · intro m c
    rw [originalLaurentCharacterTwist_single]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · subst m
      rfl
    · simp

/-- Unit-valued characters do not erase any finite coefficient or polynomial. -/
theorem originalLaurentCharacterTwist_injective (χ : Multiplicative G →* ℂˣ) :
    Function.Injective (originalLaurentCharacterTwist χ) := by
  intro p q h
  ext n
  have hc := congrArg (fun r : AddMonoidAlgebra ℂ G => r.coeff n) h
  rw [originalLaurentCharacterTwist_coefficient, originalLaurentCharacterTwist_coefficient] at hc
  exact mul_left_cancel₀ (Units.ne_zero _) hc

/-- Every genuine nonzero Laurent polynomial remains nonzero under the actual character action. -/
theorem originalLaurentCharacterTwist_ne_zero (χ : Multiplicative G →* ℂˣ)
    (p : AddMonoidAlgebra ℂ G) (hp : p ≠ 0) : originalLaurentCharacterTwist χ p ≠ 0 := by
  intro h
  apply hp
  exact originalLaurentCharacterTwist_injective χ (h.trans (map_zero _).symm)

/-- Two independent torus-character actions commute on EVERY whole finite polynomial. -/
theorem originalLaurentCharacterTwist_mul (χ ψ : Multiplicative G →* ℂˣ)
    (p : AddMonoidAlgebra ℂ G) :
    originalLaurentCharacterTwist (χ * ψ) p =
      originalLaurentCharacterTwist χ (originalLaurentCharacterTwist ψ p) := by
  ext n
  simp only [originalLaurentCharacterTwist_coefficient, MonoidHom.mul_apply, Units.val_mul]
  ring

/-- Literal character multiplication of EVERY original array row, including exterior and zero rows. -/
def originalCharacterArrayTwist (χ : Multiplicative G →* ℂˣ) (u : G → ℂ) : G → ℂ :=
  fun n => (χ (Multiplicative.ofAdd n) : ℂ) * u n

/-- Genuine finite Laurent convolution intertwines BOTH exact character actions on ALL labels. -/
theorem annihilatorArrayConvolution_characterTwist (χ : Multiplicative G →* ℂˣ)
    (p : AddMonoidAlgebra ℂ G) (u : G → ℂ) (n : G) :
    annihilatorArrayConvolution (originalLaurentCharacterTwist χ p).coeff
      (originalCharacterArrayTwist χ u) n =
      (χ (Multiplicative.ofAdd n) : ℂ) * annihilatorArrayConvolution p.coeff u n := by
  classical
  have hs : (originalLaurentCharacterTwist χ p).coeff.support = p.coeff.support := by
    ext m
    simp only [Finsupp.mem_support_iff, originalLaurentCharacterTwist_coefficient, mul_ne_zero_iff]
    constructor
    · exact And.right
    · intro hm
      exact ⟨Units.ne_zero _, hm⟩
  unfold annihilatorArrayConvolution originalCharacterArrayTwist
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [originalLaurentCharacterTwist_coefficient]
  have hc : (χ (Multiplicative.ofAdd m) : ℂ) *
      (χ (Multiplicative.ofAdd (n - m)) : ℂ) = (χ (Multiplicative.ofAdd n) : ℂ) := by
    have ha : Multiplicative.ofAdd m * Multiplicative.ofAdd (n - m) = Multiplicative.ofAdd n := by
      change Multiplicative.ofAdd (m + (n - m)) = Multiplicative.ofAdd n
      simp
    rw [← Units.val_mul, ← map_mul, ha]
  calc
    _ = ((χ (Multiplicative.ofAdd m) : ℂ) * (χ (Multiplicative.ofAdd (n - m)) : ℂ)) *
        (p.coeff m * u (n - m)) := by ring
    _ = _ := by rw [hc]

end
end MeyerGeneralProblem
