module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductOriginalRows
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ReciprocalSlabSeries
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SlabCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.SpectralConeIndex
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.OriginalSlabPivots

@[expose] public section

/-! Complete original OriginalSlabPivots for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

theorem productSlabUpperCoefficient_coordinate {s : ℕ} (block : CompactOriginalParameterBlock s) (ij : productNumeratorIndex s)
    (k n : ℕ) :
    productSlabUpperCoefficient block (productSlabCoordinateVector s ij) k n =
      if (ij.val.1 : ℕ) ≤ k ∧ (ij.val.2 : ℕ) ≤ n then
        compactOriginalUpperCoefficient block (k - ij.val.1) (n - ij.val.2) else 0 := by
  classical
  unfold productSlabUpperCoefficient
  rw [Finset.sum_eq_single ij]
  · simp only [productSlabCoordinateVector, Pi.single_eq_same, one_mul]
  · intro kl _ hkl
    have hz : productSlabCoordinateVector s ij kl = 0 := by
      simp [productSlabCoordinateVector, hkl]
    simp only [hz, zero_mul, ite_self]
  · intro h
    exact False.elim (h (Finset.mem_univ ij))

theorem productReciprocalSlabCoefficient_coordinate {s : ℕ} (block : CompactOriginalParameterBlock s) (ij : productNumeratorIndex s)
    (k n : ℕ) :
    productReciprocalSlabCoefficient block (productSlabCoordinateVector s ij) k n =
      if s - (ij.val.1 : ℕ) ≤ k ∧ s - (ij.val.2 : ℕ) ≤ n then
        compactOriginalUpperCoefficient block (k - (s - ij.val.1)) (n - (s - ij.val.2)) else 0 := by
  classical
  unfold productReciprocalSlabCoefficient
  rw [Finset.sum_eq_single ij]
  · simp only [productSlabCoordinateVector, Pi.single_eq_same, one_mul]
  · intro kl _ hkl
    have hz : productSlabCoordinateVector s ij kl = 0 := by
      simp [productSlabCoordinateVector, hkl]
    simp only [hz, zero_mul, ite_self]
  · intro h
    exact False.elim (h (Finset.mem_univ ij))

theorem productOriginalSpectralRow_coordinate_positive {s : ℕ} (block : CompactOriginalParameterBlock s) (ij : productNumeratorIndex s)
    (p : ℕ × ℕ) :
    productOriginalSpectralRow block (spectralConeIndexPoint (.inl p))
      (productSlabCoordinateVector s ij) =
      (if (ij.val.1 : ℕ) ≤ p.1 ∧ (ij.val.2 : ℕ) ≤ p.2 then
        compactOriginalUpperCoefficient block (p.1 - ij.val.1) (p.2 - ij.val.2) else 0) *
          unitPhase (-(p.2 : ℝ) / 4) := by
  calc
    _ = productSpectralCoefficient block (productSlabCoordinateVector s ij)
        (spectralConeIndexPoint (.inl p)) := productOriginalSpectralRow_eq_coefficient _ _ _
    _ = productConeIndexCoefficient block (productSlabCoordinateVector s ij) (.inl p) :=
      productSpectralCoefficient_at_label _ _ _
    _ = _ := congrArg (fun c : ℂ => c * unitPhase (-(p.2 : ℝ) / 4))
      (productSlabUpperCoefficient_coordinate block ij p.1 p.2)

theorem productOriginalSpectralRow_coordinate_negative {s : ℕ} (block : CompactOriginalParameterBlock s) (ij : productNumeratorIndex s)
    (p : {p : ℕ × ℕ // p ≠ (0, 0)}) :
    productOriginalSpectralRow block (spectralConeIndexPoint (.inr p))
      (productSlabCoordinateVector s ij) =
      -((-1 : ℂ) ^ s * (if s - (ij.val.1 : ℕ) ≤ p.val.1 ∧
          s - (ij.val.2 : ℕ) ≤ p.val.2 then
        compactOriginalUpperCoefficient block (p.val.1 - (s - ij.val.1))
          (p.val.2 - (s - ij.val.2)) else 0)) * unitPhase ((p.val.2 : ℝ) / 4) := by
  calc
    _ = productSpectralCoefficient block (productSlabCoordinateVector s ij)
        (spectralConeIndexPoint (.inr p)) := productOriginalSpectralRow_eq_coefficient _ _ _
    _ = productConeIndexCoefficient block (productSlabCoordinateVector s ij) (.inr p) :=
      productSpectralCoefficient_at_label _ _ _
    _ = _ := congrArg (fun c : ℂ => -((-1 : ℂ) ^ s * c) * unitPhase ((p.val.2 : ℝ) / 4))
      (productReciprocalSlabCoefficient_coordinate block ij p.val.1 p.val.2)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
