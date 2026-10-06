module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginalSheetProducts
public import MeyerGeneralProblem.Cardinal.Strong.NativePhysicalGap

@[expose] public section

/-! Complete labelled native and physical carriers of actual finite compact original blocks. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Every native root in the actual complete compact finite product has an original sheet/integer label. -/
theorem compactOriginalProductSheetRoots_iff_label {s : ℕ} (block : CompactOriginalParameterBlock s)
    (x : ℝ) : x ∈ compactOriginalProductSheetRoots block ↔
      ∃ i : Fin s, ∃ n : ℤ, compactOriginalRootLabel n (block.parameter i) = x := by
  rw [compactOriginalProductSheetRoots_eq_union]
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨n, hn⟩ := (sheetFlow_eq_zero_iff_label (block.parameter_bounds i).1.le
      (block.parameter_bounds i).2 x).mp hi
    exact ⟨i, n, (compactOriginalRootLabel_eq n (block.parameter_bounds i).1.le (block.range i).2.le).trans hn⟩
  · rintro ⟨i, n, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change sheetFlow (block.parameter i) (compactOriginalRootLabel n (block.parameter i)) = 0
    rw [compactOriginalRootLabel_eq n (block.parameter_bounds i).1.le (block.range i).2.le]
    exact sheetRootLabel_is_root _ (block.parameter_bounds i).1.le (block.parameter_bounds i).2 n

/-- The actual point of the COMPLETE native compact block associated with every original label. -/
def compactOriginalRootPoint {s : ℕ} (block : CompactOriginalParameterBlock s)
    (z : Fin s × ℤ) : (compactOriginalProductSheetCarrier block).subtype :=
  ⟨compactOriginalRootLabel z.2 (block.parameter z.1),
    (compactOriginalProductSheetRoots_iff_label block _).mpr ⟨z.1, z.2, rfl⟩⟩

/-- Original labels are bijective onto the WHOLE actual native compact product carrier. -/
theorem compactOriginalRootPoint_bijective {s : ℕ} (block : CompactOriginalParameterBlock s) :
    Function.Bijective (compactOriginalRootPoint block) := by
  constructor
  · rintro ⟨i, n⟩ ⟨j, l⟩ he
    have h : compactOriginalRootLabel n (block.parameter i) =
        compactOriginalRootLabel l (block.parameter j) := congrArg Subtype.val he
    rw [compactOriginalRootLabel_eq n (block.parameter_bounds i).1.le (block.range i).2.le,
      compactOriginalRootLabel_eq l (block.parameter_bounds j).1.le (block.range j).2.le] at h
    have hij : i = j := by
      by_contra hne
      exact sheetRootLabel_parameters_ne (block.parameter_bounds i).1.le (block.parameter_bounds i).2
        (block.parameter_bounds j).1.le (block.parameter_bounds j).2 (block.injective.ne hne) n l h
    subst j
    have hnl := (sheetRootLabel_strictMono _ (block.parameter_bounds i).1.le
      (block.parameter_bounds i).2).injective h
    exact Prod.ext rfl hnl
  · intro x
    obtain ⟨i, n, hn⟩ := (compactOriginalProductSheetRoots_iff_label block x.val).mp x.property
    exact ⟨(i, n), Subtype.ext hn⟩

/-- The actual positive physical carrier of the complete compact original finite product. -/
def compactOriginalPhysicalSheetCarrier {s : ℕ} (block : CompactOriginalParameterBlock s)
    (m : ℕ) (hm : 0 < m) : LocallyFiniteCarrier :=
  (compactOriginalProductSheetCarrier block).dilate (parityDilationUnit * (m : ℝ))
    (mul_pos parityDilationUnit_pos (by exact_mod_cast hm))

/-- EVERY physical root of the complete actual block, not merely a finite selected head, is labelled. -/
theorem compactOriginalPhysicalSheetCarrier_iff_label {s : ℕ} (block : CompactOriginalParameterBlock s)
    (m : ℕ) (hm : 0 < m) (x : ℝ) : x ∈ (compactOriginalPhysicalSheetCarrier block m hm).carrier ↔
      ∃ i : Fin s, ∃ n : ℤ, scaledCompactOriginalRoot m n (block.parameter i) = x := by
  change x ∈ (fun y : ℝ => (parityDilationUnit * (m : ℝ)) * y) ''
    (compactOriginalProductSheetRoots block) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, n, rfl⟩ := (compactOriginalProductSheetRoots_iff_label block y).mp hy
    exact ⟨i, n, rfl⟩
  · rintro ⟨i, n, rfl⟩
    exact ⟨compactOriginalRootLabel n (block.parameter i),
      (compactOriginalProductSheetRoots_iff_label block _).mpr ⟨i, n, rfl⟩, rfl⟩

/-- The actual compact native block has the uniform protected original gap around zero. -/
theorem compactOriginalProductSheetRoots_native_gap {s : ℕ} (block : CompactOriginalParameterBlock s)
    {x : ℝ} (hx : x ∈ compactOriginalProductSheetRoots block) : nativePhysicalGap < |x| := by
  by_contra h
  rw [compactOriginalProductSheetRoots_eq_union] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact sheetFlow_ne_zero_of_abs_le_nativePhysicalGap (block.parameter_bounds i).1.le (le_of_not_gt h) hi

/-- The complete physical block has the exact dilation of the uniform protected native gap. -/
theorem compactOriginalPhysicalSheetCarrier_gap {s : ℕ} (block : CompactOriginalParameterBlock s)
    (m : ℕ) (hm : 0 < m) {x : ℝ} (hx : x ∈ (compactOriginalPhysicalSheetCarrier block m hm).carrier) :
    (parityDilationUnit * (m : ℝ)) * nativePhysicalGap < |x| := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hc : 0 < parityDilationUnit * (m : ℝ) :=
    mul_pos parityDilationUnit_pos (by exact_mod_cast hm)
  rw [abs_mul, abs_of_pos hc]
  exact mul_lt_mul_of_pos_left (compactOriginalProductSheetRoots_native_gap block hy) hc

end

end MeyerGeneralProblem.StrongParity
