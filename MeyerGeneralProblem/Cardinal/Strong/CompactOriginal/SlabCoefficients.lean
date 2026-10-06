module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.SlabCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductResidues

@[expose] public section

/-! Original SlabCoefficients for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- The literal upper coefficient after complete finite slab convolution. -/
def productSlabUpperCoefficient {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) (k n : ℕ) : ℂ :=
  ∑ ij, if (ij.val.1 : ℕ) ≤ k ∧ (ij.val.2 : ℕ) ≤ n then
    r ij * compactOriginalUpperCoefficient block (k - ij.val.1) (n - ij.val.2) else 0

theorem productSlabUpperCoefficient_norm_le {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (k n : ℕ) :
    ‖productSlabUpperCoefficient block r k n‖ ≤
      productSlabCoefficientBound s r * ((k + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block) := by
  have hC := compactOriginalPolydiskConstant_pos block
  have hterm (ij : productNumeratorIndex s) :
      ‖if (ij.val.1 : ℕ) ≤ k ∧ (ij.val.2 : ℕ) ≤ n then
        r ij * compactOriginalUpperCoefficient block (k - ij.val.1) (n - ij.val.2) else 0‖ ≤
      ‖r ij‖ * ((k + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block) := by
    split_ifs with h
    · rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hbase : (((k - (ij.val.1 : ℕ) : ℕ) : ℝ) + 1) ≤ (k + 1 : ℝ) := by
        exact_mod_cast Nat.add_le_add_right (Nat.sub_le k (ij.val.1 : ℕ)) 1
      have hp := pow_le_pow_left₀
        (by positivity : (0 : ℝ) ≤ ((k - (ij.val.1 : ℕ) : ℕ) : ℝ) + 1) hbase s
      exact (compactOriginalUpperCoefficient_norm_le block _ _).trans
        ((div_le_div_iff_of_pos_right hC).mpr hp)
    · simp only [norm_zero]
      positivity
  calc
    _ ≤ ∑ ij : productNumeratorIndex s,
        ‖if (ij.val.1 : ℕ) ≤ k ∧ (ij.val.2 : ℕ) ≤ n then
          r ij * compactOriginalUpperCoefficient block (k - ij.val.1) (n - ij.val.2) else 0‖ := by
      unfold productSlabUpperCoefficient
      exact norm_sum_le _ _
    _ ≤ ∑ ij : productNumeratorIndex s,
        ‖r ij‖ * ((k + 1 : ℝ) ^ s / compactOriginalPolydiskConstant block) :=
      Finset.sum_le_sum (fun ij _ => hterm ij)
    _ = _ := by rw [← Finset.sum_mul]; rfl

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
