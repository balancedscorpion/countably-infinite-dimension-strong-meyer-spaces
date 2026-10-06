module

public import MeyerGeneralProblem.Cardinal.Strong.SlabCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.NatPairShiftSeries

@[expose] public section

/-! The literal complete slab convolution represents the original quotient. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Every original numerator coefficient contributes its full shifted reciprocal series. -/
theorem productSlabUpperCoefficient_hasSum (s : ℕ) (r : productNumeratorIndex s → ℂ)
    {Z W : ℂ} (hZ : ‖Z‖ < 1) (hW : ‖W‖ < 1) :
    HasSum (fun p : ℕ × ℕ => productSlabUpperCoefficient s r p.1 p.2 * Z ^ p.1 * W ^ p.2)
      (productSlabPolynomial s r Z W / productSheetPolynomial s Z W) := by
  let c : ℕ × ℕ → ℂ := fun p => productUpperCoefficient s p.1 p.2
  let A := (productSheetPolynomial s Z W)⁻¹
  have h : HasSum (fun p : ℕ × ℕ => c p * Z ^ p.1 * W ^ p.2) A :=
    productUpperCoefficient_bidisk_hasSum s hZ hW
  have hij (ij : productNumeratorIndex s) :
      HasSum (fun p : ℕ × ℕ =>
        (r ij * natPairShiftCoefficient ij.val.1 ij.val.2 c p) * Z ^ p.1 * W ^ p.2)
        (r ij * (A * Z ^ (ij.val.1 : ℕ) * W ^ (ij.val.2 : ℕ))) := by
    convert! (natPairShiftCoefficient_hasSum ij.val.1 ij.val.2 c Z W A h).mul_left
      (r ij) using 1
    funext p
    ring
  have hs := hasSum_sum (s := (Finset.univ : Finset (productNumeratorIndex s)))
    (fun ij _ => hij ij)
  convert! hs using 1
  · funext p
    unfold productSlabUpperCoefficient
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij _
    simp only [natPairShiftCoefficient, c]
    split_ifs <;> simp
  · unfold productSlabPolynomial A
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij _
    ring

/-- The full upper quotient expansion is absolutely summable inside the bidisk. -/
theorem productSlabUpperCoefficient_summable (s : ℕ) (r : productNumeratorIndex s → ℂ)
    {Z W : ℂ} (hZ : ‖Z‖ < 1) (hW : ‖W‖ < 1) :
    Summable (fun p : ℕ × ℕ => productSlabUpperCoefficient s r p.1 p.2 * Z ^ p.1 * W ^ p.2) :=
  (productSlabUpperCoefficient_hasSum s r hZ hW).summable

end

end MeyerGeneralProblem.StrongParity
