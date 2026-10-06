module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginalParameterBlock
public import MeyerGeneralProblem.Cardinal.Strong.SheetProducts
public import MeyerGeneralProblem.Carrier.Dilation

@[expose] public section

/-! Complete original finite products on actual compact parameters, with real simple roots. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The original entire product, without a real-rootedness certificate. -/
def compactOriginalComplexSheetProduct {s : ℕ} (block : CompactOriginalParameterBlock s) (z : ℂ) : ℂ :=
  ∏ i : Fin s, complexSheetFlow (block.parameter i) z

/-- The same product evaluated on the original real flow. -/
def compactOriginalRealSheetProduct {s : ℕ} (block : CompactOriginalParameterBlock s) (x : ℝ) : ℂ :=
  ∏ i : Fin s, sheetFlow (block.parameter i) x

theorem compactOriginalComplexSheetProduct_ofReal {s : ℕ} (block : CompactOriginalParameterBlock s) (x : ℝ) :
    compactOriginalComplexSheetProduct block x = compactOriginalRealSheetProduct block x := by
  simp only [compactOriginalComplexSheetProduct, compactOriginalRealSheetProduct, complexSheetFlow_ofReal]

theorem compactOriginalComplexSheetProduct_root_real {s : ℕ} (block : CompactOriginalParameterBlock s) {z : ℂ} (hroot : compactOriginalComplexSheetProduct block z = 0) :
    z.im = 0 := by
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  exact complexSheetFlow_root_real (block.parameter_bounds i).1.le
    (block.parameter_bounds i).2 hi

/-- The full product derivative; no root assumption is used. -/
theorem compactOriginalComplexSheetProduct_hasDerivAt {s : ℕ} (block : CompactOriginalParameterBlock s) (z : ℂ) :
    HasDerivAt (compactOriginalComplexSheetProduct block)
      (∑ i : Fin s, (∏ j ∈ (Finset.univ : Finset (Fin s)).erase i,
        complexSheetFlow (block.parameter j) z) *
          deriv (complexSheetFlow (block.parameter i)) z) z := by
  have hf (i : Fin s) : HasDerivAt (complexSheetFlow (block.parameter i))
      (deriv (complexSheetFlow (block.parameter i)) z) z :=
    (complexSheetFlow_hasDerivAt _ z).differentiableAt.hasDerivAt
  convert! HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hf i) using 1

/-- At a selected sheet root every other product-rule term vanishes. -/
theorem compactOriginalComplexSheetProduct_deriv_at_sheet_root {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s) {z : ℂ}
    (hroot : complexSheetFlow (block.parameter i) z = 0) :
    deriv (compactOriginalComplexSheetProduct block) z =
      (∏ j ∈ (Finset.univ : Finset (Fin s)).erase i,
        complexSheetFlow (block.parameter j) z) *
          deriv (complexSheetFlow (block.parameter i)) z := by
  rw [(compactOriginalComplexSheetProduct_hasDerivAt block z).deriv]
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hprod : (∏ k ∈ (Finset.univ : Finset (Fin s)).erase j,
        complexSheetFlow (block.parameter k) z) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩) hroot
    rw [hprod, zero_mul]
  · simp

/-- Every complex zero of the original finite product is simple. -/
theorem compactOriginalComplexSheetProduct_deriv_ne_zero {s : ℕ} (block : CompactOriginalParameterBlock s) {z : ℂ} (hroot : compactOriginalComplexSheetProduct block z = 0) :
    deriv (compactOriginalComplexSheetProduct block) z ≠ 0 := by
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  rw [compactOriginalComplexSheetProduct_deriv_at_sheet_root block i hi]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    exact complexSheetFlow_roots_disjoint (block.parameter_bounds i).1.le
      (block.parameter_bounds i).2
      ((block.injective).ne hji.symm) hi
  · exact complexSheetFlow_deriv_ne_zero (block.parameter_bounds i).1.le
      (block.parameter_bounds i).2 hi

/-- The COMPLETE real root set of the original finite product. -/
def compactOriginalProductSheetRoots {s : ℕ} (block : CompactOriginalParameterBlock s) : Set ℝ := {x | compactOriginalRealSheetProduct block x = 0}

theorem compactOriginalProductSheetRoots_eq_union {s : ℕ} (block : CompactOriginalParameterBlock s) :
    compactOriginalProductSheetRoots block = ⋃ i : Fin s, sheetRoots (block.parameter i) := by
  ext x
  simp only [compactOriginalProductSheetRoots, compactOriginalRealSheetProduct, Set.mem_ofPred_eq,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, Set.mem_iUnion, sheetRoots]

theorem compactOriginalProductSheetRoots_finite_inter_Icc {s : ℕ} (block : CompactOriginalParameterBlock s) (u v : ℝ) :
    (compactOriginalProductSheetRoots block ∩ Set.Icc u v).Finite := by
  rw [compactOriginalProductSheetRoots_eq_union, Set.iUnion_inter]
  exact Set.finite_iUnion fun i => sheetRoots_finite_inter_Icc
    (block.parameter_bounds i).1.le (block.parameter_bounds i).2 u v

/-- The full actual real product root carrier, with proved local finiteness. -/
def compactOriginalProductSheetCarrier {s : ℕ} (block : CompactOriginalParameterBlock s) : LocallyFiniteCarrier where
  carrier := compactOriginalProductSheetRoots block
  finite_inter_Icc := compactOriginalProductSheetRoots_finite_inter_Icc block

end

end MeyerGeneralProblem.StrongParity
