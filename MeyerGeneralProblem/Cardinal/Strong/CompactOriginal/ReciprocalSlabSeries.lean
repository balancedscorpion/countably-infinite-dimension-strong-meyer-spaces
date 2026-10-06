module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ReciprocalSlabSeries

@[expose] public section

/-! Original ReciprocalSlabSeries for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The full truncated convolution of the reversed original slab. -/
def productReciprocalSlabCoefficient {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (k n : ℕ) : ℂ :=
  ∑ ij, if s - (ij.val.1 : ℕ) ≤ k ∧ s - (ij.val.2 : ℕ) ≤ n then
    r ij * compactOriginalUpperCoefficient block (k - (s - ij.val.1)) (n - (s - ij.val.2)) else 0

theorem productReciprocalSlabCoefficient_norm_le {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (k n : ℕ) :
    ‖productReciprocalSlabCoefficient block r k n‖ ≤
      productSlabCoefficientBound s r * ((k + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block) := by
  have hC := compactOriginalPolydiskConstant_pos block
  have hterm (ij : productNumeratorIndex s) :
      ‖if s - (ij.val.1 : ℕ) ≤ k ∧ s - (ij.val.2 : ℕ) ≤ n then
        r ij * compactOriginalUpperCoefficient block (k - (s - ij.val.1)) (n - (s - ij.val.2)) else 0‖ ≤
      ‖r ij‖ * ((k + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block) := by
    split_ifs with h
    · rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hbase : (((k - (s - (ij.val.1 : ℕ)) : ℕ) : ℝ) + 1) ≤ (k + 1 : ℝ) := by
        exact_mod_cast Nat.add_le_add_right (Nat.sub_le k _) 1
      have hp := pow_le_pow_left₀
        (by positivity : (0 : ℝ) ≤ ((k - (s - (ij.val.1 : ℕ)) : ℕ) : ℝ) + 1) hbase s
      exact (compactOriginalUpperCoefficient_norm_le block _ _).trans
        ((div_le_div_iff_of_pos_right hC).mpr hp)
    · simp only [norm_zero]
      positivity
  calc
    _ ≤ ∑ ij : productNumeratorIndex s,
        ‖if s - (ij.val.1 : ℕ) ≤ k ∧ s - (ij.val.2 : ℕ) ≤ n then
          r ij * compactOriginalUpperCoefficient block (k - (s - ij.val.1)) (n - (s - ij.val.2)) else 0‖ := by
      unfold productReciprocalSlabCoefficient
      exact norm_sum_le _ _
    _ ≤ ∑ ij : productNumeratorIndex s,
        ‖r ij‖ * ((k + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block) :=
      Finset.sum_le_sum (fun ij _ => hterm ij)
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem productReciprocalSlabCoefficient_hasSum {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    {Z W : ℂ} (hZ : ‖Z‖ < 1) (hW : ‖W‖ < 1) :
    HasSum (fun p : ℕ × ℕ => productReciprocalSlabCoefficient block r p.1 p.2 * Z ^ p.1 * W ^ p.2)
      (productReciprocalSlabPolynomial s r Z W / compactOriginalSheetPolynomial block Z W) := by
  let c : ℕ × ℕ → ℂ := fun p => compactOriginalUpperCoefficient block p.1 p.2
  let A := (compactOriginalSheetPolynomial block Z W)⁻¹
  have h : HasSum (fun p : ℕ × ℕ => c p * Z ^ p.1 * W ^ p.2) A :=
    compactOriginalUpperCoefficient_bidisk_hasSum block hZ hW
  have hij (ij : productNumeratorIndex s) :
      HasSum (fun p : ℕ × ℕ =>
        (r ij * natPairShiftCoefficient (s - ij.val.1) (s - ij.val.2) c p) * Z ^ p.1 * W ^ p.2)
        (r ij * (A * Z ^ (s - (ij.val.1 : ℕ)) * W ^ (s - (ij.val.2 : ℕ)))) := by
    convert! (natPairShiftCoefficient_hasSum (s - ij.val.1) (s - ij.val.2) c Z W A h).mul_left
      (r ij) using 1
    funext p
    ring
  have hs := hasSum_sum (s := (Finset.univ : Finset (productNumeratorIndex s)))
    (fun ij _ => hij ij)
  convert! hs using 1
  · funext p
    unfold productReciprocalSlabCoefficient
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij _
    simp only [natPairShiftCoefficient, c]
    split_ifs <;> simp
  · unfold productReciprocalSlabPolynomial A
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij _
    ring

theorem productReciprocalSlabCoefficient_zero_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    productReciprocalSlabCoefficient block r 0 0 = 0 := by
  unfold productReciprocalSlabCoefficient
  apply Finset.sum_eq_zero
  intro ij _
  have hij : ¬ (s - (ij.val.1 : ℕ) ≤ 0 ∧ s - (ij.val.2 : ℕ) ≤ 0) := by
    intro h
    have hi : (ij.val.1 : ℕ) = s := by omega
    have hj : (ij.val.2 : ℕ) = s := by omega
    exact ij.property (by apply Prod.ext <;> apply Fin.ext <;> assumption)
  simp only [hij, ite_false]

/-- The actual lower rational expansion includes the original product sign. -/
def productSlabLowerCoefficient {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (k n : ℕ) : ℂ := (-1 : ℂ) ^ s * productReciprocalSlabCoefficient block r k n

theorem productSlabLowerCoefficient_norm_le {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (k n : ℕ) :
    ‖productSlabLowerCoefficient block r k n‖ ≤
      productSlabCoefficientBound s r * ((k + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block) := by
  simpa only [productSlabLowerCoefficient, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul] using productReciprocalSlabCoefficient_norm_le block r k n

theorem productSlabLowerCoefficient_zero_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    productSlabLowerCoefficient block r 0 0 = 0 := by
  simp only [productSlabLowerCoefficient, productReciprocalSlabCoefficient_zero_zero, mul_zero]

theorem productSlabLowerCoefficient_hasSum {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    {Z W : ℂ} (hZ : ‖Z‖ < 1) (hW : ‖W‖ < 1) :
    HasSum (fun p : ℕ × ℕ => productSlabLowerCoefficient block r p.1 p.2 * Z ^ p.1 * W ^ p.2)
      ((-1 : ℂ) ^ s *
        (productReciprocalSlabPolynomial s r Z W / compactOriginalSheetPolynomial block Z W)) := by
  convert! (productReciprocalSlabCoefficient_hasSum block r hZ hW).mul_left
    ((-1 : ℂ) ^ s) using 1
  funext p
  unfold productSlabLowerCoefficient
  ring

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
