module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginalLabelledRoots
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginalBidiskCoefficients

@[expose] public section

/-! Actual finite compact source carriers and physical-root names from the coupled construction. -/

namespace MeyerGeneralProblem.StrongParity

/-- Every physical root of an actual coupled compact block has an ordinary rational name program. -/
def coupledCompactOriginalPhysicalRootName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s m : ℕ) (i : Fin s) (n : ℤ) (p : ℕ) : ℚ :=
  rationalNamedScaledOriginalRootApprox
    (coupledOriginalParameterNames scales hpos disjointOriginalParameterSlot (offset + i.val)).val m n p

noncomputable section

/-- EVERY actual labelled physical root of the constructed block has the implemented binary error. -/
theorem coupledCompactOriginalPhysicalRootName_error (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s m : ℕ) (i : Fin s) (n : ℤ) (p : ℕ) :
    |(coupledCompactOriginalPhysicalRootName scales hpos offset s m i n p : ℝ) -
      scaledCompactOriginalRoot m n ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter i)| ≤
        1 / (2 : ℝ) ^ p :=
  rationalNamedScaledOriginalRootApprox_error _ m n
    (coupledOriginalParameterValue_compact scales hpos disjointOriginalParameterSlot (offset + i.val))
    (coupledOriginalParameterNames_range scales hpos disjointOriginalParameterSlot (offset + i.val))
    (coupledOriginalParameterNames_error scales hpos disjointOriginalParameterSlot (offset + i.val)) p

/-- The exact finite same-scale frame identifies every physical block root with its original coupled root. -/
theorem coupledCompactOriginalPhysicalRoot_eq (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s m : ℕ) (hscale : ∀ i : Fin s, scales (offset + i.val) = m) (i : Fin s) (n : ℤ) :
    scaledCompactOriginalRoot m n ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter i) =
      coupledOriginalPhysicalRoot scales hpos disjointOriginalParameterSlot (offset + i.val) n := by
  simp only [coupledOriginalPhysicalRoot, coupledCompactOriginalParameterBlock, hscale i]

/-- Every root of the COMPLETE constructed same-scale compact source block lies outside Gamma_Q. -/
theorem coupledCompactOriginalPhysicalCarrier_not_mem (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s m : ℕ) (hm : 0 < m) (hscale : ∀ i : Fin s, scales (offset + i.val) = m)
    {x : ℝ} (hx : x ∈ (compactOriginalPhysicalSheetCarrier
      (coupledCompactOriginalParameterBlock scales hpos offset s) m hm).carrier) :
    x ∉ parityRationalCoarseModule := by
  obtain ⟨i, n, he⟩ := (compactOriginalPhysicalSheetCarrier_iff_label _ m hm x).mp hx
  rw [coupledCompactOriginalPhysicalRoot_eq scales hpos offset s m hscale] at he
  rw [← he]
  exact coupledOriginalPhysicalRoot_not_mem scales hpos disjointOriginalParameterSlot (offset + i.val) n

/-- Every distinct root difference in the WHOLE actual same-scale compact source block avoids Gamma_Q. -/
theorem coupledCompactOriginalPhysicalCarrier_difference_not_mem (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s m : ℕ) (hm : 0 < m)
    (hscale : ∀ i : Fin s, scales (offset + i.val) = m) {x y : ℝ}
    (hx : x ∈ (compactOriginalPhysicalSheetCarrier
      (coupledCompactOriginalParameterBlock scales hpos offset s) m hm).carrier)
    (hy : y ∈ (compactOriginalPhysicalSheetCarrier
      (coupledCompactOriginalParameterBlock scales hpos offset s) m hm).carrier) (hxy : x ≠ y) :
    x - y ∉ parityRationalCoarseModule := by
  obtain ⟨i, n, he⟩ := (compactOriginalPhysicalSheetCarrier_iff_label _ m hm x).mp hx
  obtain ⟨j, l, hf⟩ := (compactOriginalPhysicalSheetCarrier_iff_label _ m hm y).mp hy
  rw [coupledCompactOriginalPhysicalRoot_eq scales hpos offset s m hscale] at he hf
  rw [← he, ← hf]
  apply coupledOriginalPhysicalRoot_difference_not_mem scales hpos disjointOriginalParameterSlot
    (offset + i.val) (offset + j.val) n l
  intro hij
  have hr := congrArg (fun z : ℕ × ℤ =>
    coupledOriginalPhysicalRoot scales hpos disjointOriginalParameterSlot z.1 z.2) hij
  exact hxy (he.symm.trans (hr.trans hf))

/-- Every sum, including self-sums, in the COMPLETE actual same-scale source block avoids Gamma_Q. -/
theorem coupledCompactOriginalPhysicalCarrier_sum_not_mem (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s m : ℕ) (hm : 0 < m)
    (hscale : ∀ i : Fin s, scales (offset + i.val) = m) {x y : ℝ}
    (hx : x ∈ (compactOriginalPhysicalSheetCarrier
      (coupledCompactOriginalParameterBlock scales hpos offset s) m hm).carrier)
    (hy : y ∈ (compactOriginalPhysicalSheetCarrier
      (coupledCompactOriginalParameterBlock scales hpos offset s) m hm).carrier) :
    x + y ∉ parityRationalCoarseModule := by
  obtain ⟨i, n, he⟩ := (compactOriginalPhysicalSheetCarrier_iff_label _ m hm x).mp hx
  obtain ⟨j, l, hf⟩ := (compactOriginalPhysicalSheetCarrier_iff_label _ m hm y).mp hy
  rw [coupledCompactOriginalPhysicalRoot_eq scales hpos offset s m hscale] at he hf
  rw [← he, ← hf]
  exact coupledOriginalPhysicalRoot_sum_not_mem scales hpos disjointOriginalParameterSlot
    (offset + i.val) (offset + j.val) n l

end

end MeyerGeneralProblem.StrongParity
