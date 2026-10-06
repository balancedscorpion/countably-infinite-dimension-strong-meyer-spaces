module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductOriginalRows
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ReciprocalSlabSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SlabCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralConeIndex
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductMiddleGap

@[expose] public section

/-! Complete original ProductMiddleGap for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

theorem productInteriorMonomial_upper_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (h : ℕ) (hh : h < s) (k n : ℕ)
    (hk : k < h ∨ n < h) :
    productSlabUpperCoefficient block (productInteriorMonomial s h hh) k n = 0 := by
  classical
  unfold productSlabUpperCoefficient
  apply Finset.sum_eq_zero
  intro ij _
  by_cases hij : ij = productInteriorIndex s h hh
  · subst ij
    have hnot : ¬(h ≤ k ∧ h ≤ n) := by omega
    change (if h ≤ k ∧ h ≤ n then _ else 0) = 0
    rw [ite_eq_right hnot]
  · have hz : productInteriorMonomial s h hh ij = 0 := by
      simp [productInteriorMonomial, hij]
    simp only [hz, zero_mul, ite_self]

theorem productInteriorMonomial_lower_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (h : ℕ) (hh : h < s) (k n : ℕ)
    (hk : k < s - h ∨ n < s - h) :
    productSlabLowerCoefficient block (productInteriorMonomial s h hh) k n = 0 := by
  classical
  unfold productSlabLowerCoefficient
  have hz : productReciprocalSlabCoefficient block (productInteriorMonomial s h hh) k n = 0 := by
    unfold productReciprocalSlabCoefficient
    apply Finset.sum_eq_zero
    intro ij _
    by_cases hij : ij = productInteriorIndex s h hh
    · subst ij
      have hnot : ¬(s - h ≤ k ∧ s - h ≤ n) := by omega
      change (if s - h ≤ k ∧ s - h ≤ n then _ else 0) = 0
      rw [ite_eq_right hnot]
    · have hz : productInteriorMonomial s h hh ij = 0 := by
        simp [productInteriorMonomial, hij]
      simp only [hz, zero_mul, ite_self]
  rw [hz, mul_zero]

theorem productMiddleMonomial_original_head_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (x : spectralConeCarrier.subtype) (hx : |(x : ℝ)| ≤ ((s / 2 : ℕ) : ℝ) / 2) :
    productOriginalSpectralRow block x (productMiddleMonomial s hs) = 0 := by
  obtain ⟨p, rfl⟩ := spectralConeIndexPoint_bijective.2 x
  rw [productOriginalSpectralRow_eq_coefficient, productSpectralCoefficient_at_label]
  have hh : 0 < (s / 2 : ℕ) := by omega
  have hhr : 0 < ((s / 2 : ℕ) : ℝ) := by exact_mod_cast hh
  rcases p with p | p
  · have hk : p.1 < s / 2 := by
      have hb := (positiveConeFrequency_coordinate_le p).1
      simp only [spectralConeIndexPoint, spectralConeIndexFrequency,
        abs_of_nonneg (positiveConeFrequency_nonneg p)] at hx
      exact_mod_cast (show (p.1 : ℝ) < ((s / 2 : ℕ) : ℝ) by linarith)
    simp only [productConeIndexCoefficient, productMiddleMonomial,
      productInteriorMonomial_upper_zero _ _ _ _ _ (Or.inl hk), zero_mul]
  · have hk : p.val.1 < s - s / 2 := by
      have hb := (positiveConeFrequency_coordinate_le p.val).1
      simp only [spectralConeIndexPoint, spectralConeIndexFrequency, abs_neg,
        abs_of_nonneg (positiveConeFrequency_nonneg p.val)] at hx
      have hk' : p.val.1 < s / 2 := by
        exact_mod_cast (show (p.val.1 : ℝ) < ((s / 2 : ℕ) : ℝ) by linarith)
      omega
    simp only [productConeIndexCoefficient, productMiddleMonomial,
      productInteriorMonomial_lower_zero _ _ _ _ _ (Or.inl hk), neg_zero, zero_mul]

theorem productMiddleMonomial_mem_original_head_kernel {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (F : Set ℝ) (hF : ∀ x ∈ F, |x| ≤ ((s / 2 : ℕ) : ℝ) / 2) :
    productMiddleMonomial s hs ∈ productOriginalDeletionKernel block ∅ F := by
  rw [mem_productOriginalDeletionKernel_iff]
  exact ⟨by simp, fun x hx => productMiddleMonomial_original_head_zero block hs x (hF x hx)⟩

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
