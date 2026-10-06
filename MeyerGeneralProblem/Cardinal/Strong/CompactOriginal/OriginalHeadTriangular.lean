module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalHeadLabels
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.OriginalSlabPivots
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductOriginalRows
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadTriangular

@[expose] public section

/-! Complete original OriginalHeadTriangular for internally constructed compact blocks.
The actual full head rows, original residues and whole-space quantifiers are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

theorem productOriginalHeadRow_pivot_ne_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (p : productOriginalHeadLabel s) :
    productOriginalHeadRow block p
      (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs p)) ≠ 0 := by
  rcases p with ⟨p | p, hp⟩
  · change productOriginalSpectralRow block (spectralConeIndexPoint (.inl p))
      (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs ⟨.inl p, hp⟩)) ≠ 0
    rw [productOriginalSpectralRow_coordinate_positive]
    change (if p.1 ≤ p.1 ∧ p.2 ≤ p.2 then
      compactOriginalUpperCoefficient block (p.1 - p.1) (p.2 - p.2) else 0) * unitPhase _ ≠ 0
    simp only [le_refl, and_self, ite_true, Nat.sub_self,
      compactOriginalUpperCoefficient_zero_zero, one_mul]
    exact Complex.exp_ne_zero _
  · have hlt := productOriginalHeadCoordinates_lt s hs ⟨.inr p, hp⟩
    change p.val.1 < s ∧ p.val.2 < s at hlt
    change productOriginalSpectralRow block (spectralConeIndexPoint (.inr p))
      (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs ⟨.inr p, hp⟩)) ≠ 0
    rw [productOriginalSpectralRow_coordinate_negative]
    change -((-1 : ℂ) ^ s * (if s - (s - p.val.1) ≤ p.val.1 ∧
      s - (s - p.val.2) ≤ p.val.2 then compactOriginalUpperCoefficient block
      (p.val.1 - (s - (s - p.val.1))) (p.val.2 - (s - (s - p.val.2))) else 0)) * unitPhase _ ≠ 0
    rw [Nat.sub_sub_self hlt.1.le, Nat.sub_sub_self hlt.2.le]
    simp only [le_refl, and_self, ite_true, Nat.sub_self,
      compactOriginalUpperCoefficient_zero_zero, mul_one]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))) (Complex.exp_ne_zero _)

theorem productOriginalHeadRow_cross_pivot_zero {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s)
    (p q : productOriginalHeadLabel s) (hpq : p ≠ q)
    (hdegree : productOriginalHeadDegree s p ≤ productOriginalHeadDegree s q) :
    productOriginalHeadRow block p
      (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs q)) = 0 := by
  rcases p with ⟨p | p, hp⟩ <;> rcases q with ⟨q | q, hq⟩
  · have hnot : ¬(q.1 ≤ p.1 ∧ q.2 ≤ p.2) := by
      intro h
      change p.1 + p.2 ≤ q.1 + q.2 at hdegree
      apply hpq
      apply Subtype.ext
      apply congrArg Sum.inl
      exact Prod.ext (by omega) (by omega)
    change productOriginalSpectralRow block (spectralConeIndexPoint (.inl p))
      (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs ⟨.inl q, hq⟩)) = 0
    rw [productOriginalSpectralRow_coordinate_positive]
    change (if q.1 ≤ p.1 ∧ q.2 ≤ p.2 then _ else 0) * unitPhase _ = 0
    rw [ite_eq_right hnot, zero_mul]
  · have hlow := productOriginalHead_low_lt_high s hs ⟨.inl p, hp⟩ ⟨.inr q, hq⟩
    change p.1 < s - q.val.1 ∧ p.2 < s - q.val.2 at hlow
    have hnot : ¬(s - q.val.1 ≤ p.1 ∧ s - q.val.2 ≤ p.2) := by omega
    change productOriginalSpectralRow block (spectralConeIndexPoint (.inl p))
      (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs ⟨.inr q, hq⟩)) = 0
    rw [productOriginalSpectralRow_coordinate_positive]
    change (if s - q.val.1 ≤ p.1 ∧ s - q.val.2 ≤ p.2 then _ else 0) * unitPhase _ = 0
    rw [ite_eq_right hnot, zero_mul]
  · have hlow := productOriginalHead_low_lt_high s hs ⟨.inl q, hq⟩ ⟨.inr p, hp⟩
    change q.1 < s - p.val.1 ∧ q.2 < s - p.val.2 at hlow
    have hnot : ¬(s - q.1 ≤ p.val.1 ∧ s - q.2 ≤ p.val.2) := by omega
    change productOriginalSpectralRow block (spectralConeIndexPoint (.inr p))
      (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs ⟨.inl q, hq⟩)) = 0
    rw [productOriginalSpectralRow_coordinate_negative]
    change -((-1 : ℂ) ^ s * (if s - q.1 ≤ p.val.1 ∧ s - q.2 ≤ p.val.2 then _ else 0)) *
      unitPhase _ = 0
    rw [ite_eq_right hnot, mul_zero, neg_zero, zero_mul]
  · have hlt := productOriginalHeadCoordinates_lt s hs ⟨.inr q, hq⟩
    change q.val.1 < s ∧ q.val.2 < s at hlt
    have hnot : ¬(q.val.1 ≤ p.val.1 ∧ q.val.2 ≤ p.val.2) := by
      intro h
      change p.val.1 + p.val.2 ≤ q.val.1 + q.val.2 at hdegree
      apply hpq
      apply Subtype.ext
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Prod.ext (by omega) (by omega)
    change productOriginalSpectralRow block (spectralConeIndexPoint (.inr p))
      (productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs ⟨.inr q, hq⟩)) = 0
    rw [productOriginalSpectralRow_coordinate_negative]
    change -((-1 : ℂ) ^ s * (if s - (s - q.val.1) ≤ p.val.1 ∧
      s - (s - q.val.2) ≤ p.val.2 then _ else 0)) * unitPhase _ = 0
    rw [Nat.sub_sub_self hlt.1.le, Nat.sub_sub_self hlt.2.le,
      ite_eq_right hnot, mul_zero, neg_zero, zero_mul]

/-- ALL original signed head rows are independent on the whole original slab.
In particular any noncoarse retained subfamily remains independent. -/
theorem productOriginalHeadRows_linearIndependent {s : ℕ} (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s) :
    LinearIndependent ℂ (productOriginalHeadRow block) :=
  UniformDiscrete.linearIndependent_of_original_triangular_pivots
    (productOriginalHeadRow block)
    (fun p => productSlabCoordinateVector s (productOriginalHeadPivotIndex s hs p))
    (productOriginalHeadDegree s) (productOriginalHeadRow_pivot_ne_zero block hs)
    (productOriginalHeadRow_cross_pivot_zero block hs)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal
