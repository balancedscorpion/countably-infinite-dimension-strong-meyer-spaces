module

public import MeyerGeneralProblem.Cardinal.Strong.PositiveOriginalNativeDilation
public import MeyerGeneralProblem.Cardinal.Strong.SlabCoefficients

@[expose] public section

/-! The entire original slab, using the existing productNumeratorIndex type.
Only its top corner is excluded. The inverse quarter phase converts unphased
polynomial coefficients into the actual phased native numerator coefficients. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Literal pair of native natural labels of the existing slab index. -/
def originalNativeSlabLabel (s : ℕ) (ij : productNumeratorIndex s) : ℕ × ℕ :=
  (ij.val.1.val, ij.val.2.val)

/-- The full native slab contains no duplicated coordinate labels. -/
theorem originalNativeSlabLabel_injective (s : ℕ) :
    Function.Injective (originalNativeSlabLabel s) := by
  intro a b h
  exact Subtype.ext (Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h)))

/-- Every original slab label lies in its full native square. -/
theorem originalNativeSlabLabel_bounds (s : ℕ) (ij : productNumeratorIndex s) :
    (originalNativeSlabLabel s ij).1 ≤ s ∧ (originalNativeSlabLabel s ij).2 ≤ s :=
  ⟨Nat.le_of_lt_succ ij.val.1.isLt, Nat.le_of_lt_succ ij.val.2.isLt⟩

/-- Exactly the top corner is excluded by the existing native type. -/
theorem originalNativeSlabLabel_ne_top (s : ℕ) (ij : productNumeratorIndex s) :
    originalNativeSlabLabel s ij ≠ (s, s) := by
  intro h
  exact ij.property (Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h)))

/-- The full existing slab coefficient function as a positive polynomial. -/
def originalNativeSlabPositivePolynomial (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  ∑ ij, AddMonoidAlgebra.single (originalNativeSlabLabel s ij) (r ij)

/-- The entire original native coefficient function is retained exactly. -/
theorem originalNativeSlabPositivePolynomial_coefficient (s : ℕ)
    (r : productNumeratorIndex s → ℂ) (ij : productNumeratorIndex s) :
    (originalNativeSlabPositivePolynomial s r).coeff (originalNativeSlabLabel s ij) = r ij := by
  classical
  simp only [originalNativeSlabPositivePolynomial, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single]
  rw [Finset.sum_eq_single ij]
  · exact Finsupp.single_eq_same
  · intro j _ hji
    exact Finsupp.single_eq_of_ne (fun he => hji (originalNativeSlabLabel_injective s he.symm))
  · simp

/-- Every coefficient in the ENTIRE native square is reconstructed. -/
theorem originalNativeSlabPositivePolynomial_reconstruct (s : ℕ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : OriginalPositiveInSquare p s)
    (htop : p.coeff (s, s) = 0) :
    originalNativeSlabPositivePolynomial s (fun ij => p.coeff (originalNativeSlabLabel s ij)) = p := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  ext n
  by_cases hn : n.1 ≤ s ∧ n.2 ≤ s ∧ n ≠ (s, s)
  · let ij : productNumeratorIndex s :=
      ⟨(⟨n.1, Nat.lt_succ_of_le hn.1⟩, ⟨n.2, Nat.lt_succ_of_le hn.2.1⟩),
        fun h => hn.2.2 (Prod.ext (congrArg (fun a => a.1.val) h) (congrArg (fun a => a.2.val) h))⟩
    exact originalNativeSlabPositivePolynomial_coefficient s _ ij
  · have hz : p.coeff n = 0 := by
      by_contra hc
      have hb := hp n (Finsupp.mem_support_iff.mpr hc)
      have hnt : n ≠ (s, s) := fun he => hc (he ▸ htop)
      exact hn ⟨hb.1, hb.2, hnt⟩
    rw [hz]
    simp only [originalNativeSlabPositivePolynomial, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single]
    apply Finset.sum_eq_zero
    intro ij _
    apply Finsupp.single_eq_of_ne
    intro he
    apply hn
    rw [he]
    exact ⟨(originalNativeSlabLabel_bounds s ij).1,
      (originalNativeSlabLabel_bounds s ij).2, originalNativeSlabLabel_ne_top s ij⟩

/-- The algebra polynomial evaluates to the literal existing slab polynomial. -/
theorem originalNativeSlabPositivePolynomial_evaluation (s : ℕ)
    (r : productNumeratorIndex s → ℂ) (Z W : ℂ) :
    originalPositiveTorusEvaluation Z W (originalNativeSlabPositivePolynomial s r) =
      productSlabPolynomial s r Z W := by
  simp only [originalNativeSlabPositivePolynomial, map_sum, originalPositiveTorusEvaluation_single,
    originalNativeSlabLabel, productSlabPolynomial, mul_assoc]

/-- Genuine native numerator coefficients: the quarter phase is removed once
per W exponent, independently of the coordinate dilation. -/
def originalNativePhasedSlabCoefficients (s : ℕ) (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    productNumeratorIndex s → ℂ :=
  fun ij => p.coeff (originalNativeSlabLabel s ij) * (complexUnitPhase (-1 / 4))⁻¹ ^ ij.val.2.val

/-- The actual native slab with its quarter phase inserted AFTER the W power. -/
def originalPhasedSlabPositivePolynomial (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  originalNativeSlabPositivePolynomial s (fun ij => r ij * complexUnitPhase (-1 / 4) ^ ij.val.2.val)

theorem originalPhasedSlabPositivePolynomial_reconstruct (s : ℕ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : OriginalPositiveInSquare p s)
    (htop : p.coeff (s, s) = 0) :
    originalPhasedSlabPositivePolynomial s (originalNativePhasedSlabCoefficients s p) = p := by
  have hc : (fun ij : productNumeratorIndex s => originalNativePhasedSlabCoefficients s p ij *
      complexUnitPhase (-1 / 4) ^ ij.val.2.val) = fun ij => p.coeff (originalNativeSlabLabel s ij) := by
    funext ij
    simp only [originalNativePhasedSlabCoefficients, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ originalQuarterPhase_ne_zero, one_pow, mul_one]
  rw [originalPhasedSlabPositivePolynomial, hc]
  exact originalNativeSlabPositivePolynomial_reconstruct s p hp htop

/-- Literal phase conversion at arbitrary complex coordinates. -/
theorem originalPhasedSlabPositivePolynomial_evaluation (s : ℕ)
    (r : productNumeratorIndex s → ℂ) (Z W : ℂ) :
    originalPositiveTorusEvaluation Z W (originalPhasedSlabPositivePolynomial s r) =
      productSlabPolynomial s r Z (complexUnitPhase (-1 / 4) * W) := by
  rw [originalPhasedSlabPositivePolynomial, originalNativeSlabPositivePolynomial_evaluation]
  unfold productSlabPolynomial
  apply Finset.sum_congr rfl
  intro ij _
  simp only [mul_pow]
  ring

/-- Dilation powers the coordinates before the single original quarter phase. -/
theorem originalPhasedSlabPositivePolynomial_dilation_evaluation (d s : ℕ)
    (r : productNumeratorIndex s → ℂ) (Z W : ℂ) :
    originalPositiveTorusEvaluation Z W
      (originalPositiveDilation d (originalPhasedSlabPositivePolynomial s r)) =
        productSlabPolynomial s r (Z ^ d) (complexUnitPhase (-1 / 4) * W ^ d) := by
  rw [originalPositiveDilation_evaluation, originalPhasedSlabPositivePolynomial_evaluation]

/-- The exact original real flow, including the unpowered quarter phase. -/
theorem originalPhasedSlabPositivePolynomial_dilation_onFlow (d s : ℕ)
    (r : productNumeratorIndex s → ℂ) (x : ℝ) :
    originalPositiveTorusEvaluation (unitPhase x) (unitPhase (beta * x))
      (originalPositiveDilation d (originalPhasedSlabPositivePolynomial s r)) =
        productSlabNumerator s r ((d : ℝ) * x) := by
  have hp (t : ℝ) : unitPhase t ^ d = unitPhase ((d : ℝ) * t) := by
    unfold unitPhase
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [originalPhasedSlabPositivePolynomial_dilation_evaluation, hp x, hp (beta * x)]
  have hw : complexUnitPhase (-1 / 4) * unitPhase ((d : ℝ) * (beta * x)) =
      unitPhase (beta * ((d : ℝ) * x) - 1 / 4) := by
    have he : complexUnitPhase (-1 / 4) = unitPhase (-1 / 4) := by
      convert complexUnitPhase_ofReal (-1 / 4) using 1
      norm_num
    rw [he, ← unitPhase_add]
    congr 1
    ring
  rw [hw, productSlabPolynomial_onFlow]

end
end MeyerGeneralProblem.StrongParity
