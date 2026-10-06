module

public import MeyerGeneralProblem.Cardinal.Strong.SheetCounting

@[expose] public section

/-!
# The literal finite products of the original sheets

The parameters are exactly `j/(s+1)` for `1 <= j <= s`. Their entire
product has only real simple zeros. Its complete real root set is the
finite union of the actual sheets, hence locally finite.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The original distinct parameters, indexed from zero in `Fin s`. -/
def productSheetParameter (s : ℕ) (i : Fin s) : ℝ := ((i : ℕ) + 1 : ℕ) / (s + 1 : ℕ)

theorem productSheetParameter_bounds (s : ℕ) (i : Fin s) :
    0 < productSheetParameter s i ∧ productSheetParameter s i < 1 := by
  unfold productSheetParameter
  constructor
  · positivity
  · apply (div_lt_one (by positivity : (0 : ℝ) < (s + 1 : ℕ))).mpr
    exact_mod_cast Nat.add_lt_add_right i.isLt 1

theorem productSheetParameter_injective (s : ℕ) : Function.Injective (productSheetParameter s) := by
  intro i j hij
  have hd : ((s + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have heq := (div_left_inj' hd).mp hij
  have hval : (i : ℕ) + 1 = (j : ℕ) + 1 := by exact_mod_cast heq
  apply Fin.ext
  omega

/-- The original entire product, without a real-rootedness certificate. -/
def complexSheetProduct (s : ℕ) (z : ℂ) : ℂ :=
  ∏ i : Fin s, complexSheetFlow (productSheetParameter s i) z

/-- The same product evaluated on the original real flow. -/
def realSheetProduct (s : ℕ) (x : ℝ) : ℂ :=
  ∏ i : Fin s, sheetFlow (productSheetParameter s i) x

theorem complexSheetProduct_ofReal (s : ℕ) (x : ℝ) :
    complexSheetProduct s x = realSheetProduct s x := by
  simp only [complexSheetProduct, realSheetProduct, complexSheetFlow_ofReal]

theorem complexSheetProduct_root_real (s : ℕ) {z : ℂ} (hroot : complexSheetProduct s z = 0) :
    z.im = 0 := by
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  exact complexSheetFlow_root_real (productSheetParameter_bounds s i).1.le
    (productSheetParameter_bounds s i).2 hi

theorem complexSheetFlow_roots_disjoint {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hab : a ≠ b) {z : ℂ} (hroot : complexSheetFlow a z = 0) :
    complexSheetFlow b z ≠ 0 := by
  have hz : z = (z.re : ℂ) := by
    apply Complex.ext_iff.mpr
    constructor
    · simp only [Complex.ofReal_re]
    · simpa only [Complex.ofReal_im] using complexSheetFlow_root_real ha ha1 hroot
  rw [hz, complexSheetFlow_ofReal] at hroot ⊢
  have habC : (a : ℂ) ≠ (b : ℂ) := fun h => hab (Complex.ofReal_inj.mp h)
  exact quarterFlow_sheet_roots_disjoint habC z.re hroot

/-- The full product derivative; no root assumption is used. -/
theorem complexSheetProduct_hasDerivAt (s : ℕ) (z : ℂ) :
    HasDerivAt (complexSheetProduct s)
      (∑ i : Fin s, (∏ j ∈ (Finset.univ : Finset (Fin s)).erase i,
        complexSheetFlow (productSheetParameter s j) z) *
          deriv (complexSheetFlow (productSheetParameter s i)) z) z := by
  have hf (i : Fin s) : HasDerivAt (complexSheetFlow (productSheetParameter s i))
      (deriv (complexSheetFlow (productSheetParameter s i)) z) z :=
    (complexSheetFlow_hasDerivAt _ z).differentiableAt.hasDerivAt
  convert! HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hf i) using 1

/-- At a selected sheet root every other product-rule term vanishes. -/
theorem complexSheetProduct_deriv_at_sheet_root (s : ℕ) (i : Fin s) {z : ℂ}
    (hroot : complexSheetFlow (productSheetParameter s i) z = 0) :
    deriv (complexSheetProduct s) z =
      (∏ j ∈ (Finset.univ : Finset (Fin s)).erase i,
        complexSheetFlow (productSheetParameter s j) z) *
          deriv (complexSheetFlow (productSheetParameter s i)) z := by
  rw [(complexSheetProduct_hasDerivAt s z).deriv]
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hprod : (∏ k ∈ (Finset.univ : Finset (Fin s)).erase j,
        complexSheetFlow (productSheetParameter s k) z) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩) hroot
    rw [hprod, zero_mul]
  · simp

/-- Every complex zero of the original finite product is simple. -/
theorem complexSheetProduct_deriv_ne_zero (s : ℕ) {z : ℂ} (hroot : complexSheetProduct s z = 0) :
    deriv (complexSheetProduct s) z ≠ 0 := by
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  rw [complexSheetProduct_deriv_at_sheet_root s i hi]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    exact complexSheetFlow_roots_disjoint (productSheetParameter_bounds s i).1.le
      (productSheetParameter_bounds s i).2
      ((productSheetParameter_injective s).ne hji.symm) hi
  · exact complexSheetFlow_deriv_ne_zero (productSheetParameter_bounds s i).1.le
      (productSheetParameter_bounds s i).2 hi

/-- The COMPLETE real root set of the original finite product. -/
def productSheetRoots (s : ℕ) : Set ℝ := {x | realSheetProduct s x = 0}

theorem productSheetRoots_eq_union (s : ℕ) :
    productSheetRoots s = ⋃ i : Fin s, sheetRoots (productSheetParameter s i) := by
  ext x
  simp only [productSheetRoots, realSheetProduct, Set.mem_ofPred_eq,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, Set.mem_iUnion, sheetRoots]

theorem productSheetRoots_finite_inter_Icc (s : ℕ) (u v : ℝ) :
    (productSheetRoots s ∩ Set.Icc u v).Finite := by
  rw [productSheetRoots_eq_union, Set.iUnion_inter]
  exact Set.finite_iUnion fun i => sheetRoots_finite_inter_Icc
    (productSheetParameter_bounds s i).1.le (productSheetParameter_bounds s i).2 u v

/-- The full actual real product root carrier, with proved local finiteness. -/
def productSheetCarrier (s : ℕ) : LocallyFiniteCarrier where
  carrier := productSheetRoots s
  finite_inter_Icc := productSheetRoots_finite_inter_Icc s

end

end MeyerGeneralProblem.StrongParity
