module

public import MeyerGeneralProblem.Cardinal.Strong.SheetPowerSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section

/-! Actual products of finitely many absolutely convergent complex series.
This elementary reindexing retains the complete multi-index family. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Split a natural multi-index into its first coordinate and its tail. -/
def finNatVectorSplit (s : ℕ) : (Fin (s + 1) → ℕ) ≃ ℕ × (Fin s → ℕ) where
  toFun v := (v 0, fun i => v i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv v := Fin.cons_self_tail v
  right_inv p := by cases p; rfl

/-- The complete multi-index series sums to the product of the actual sums. -/
theorem hasSum_finiteSeriesProduct (s : ℕ) (f : Fin s → ℕ → ℂ) (a : Fin s → ℂ)
    (hf : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun v : Fin s → ℕ => ∏ i : Fin s, f i (v i)) (∏ i : Fin s, a i) := by
  induction s with
  | zero =>
    let _ : Fintype (Fin 0 → ℕ) := Fintype.ofSubsingleton (fun _ => 0)
    simp
  | succ s ih =>
    have hrest := ih (fun i => f i.succ) (fun i => a i.succ) (fun i => hf i.succ)
    have hzeroNorm : Summable (fun k => ‖f 0 k‖) := (hf 0).summable.norm
    have hrestNorm : Summable (fun v : Fin s → ℕ => ‖∏ i : Fin s, f i.succ (v i)‖) :=
      hrest.summable.norm
    have hmul : Summable (fun p : ℕ × (Fin s → ℕ) =>
        f 0 p.1 * ∏ i : Fin s, f i.succ (p.2 i)) :=
      summable_mul_of_summable_norm (R := ℂ) (f := f 0)
        (g := fun v : Fin s → ℕ => ∏ i : Fin s, f i.succ (v i)) hzeroNorm hrestNorm
    have hm := (hf 0).mul hrest hmul
    have htransport := (finNatVectorSplit s).hasSum_iff.mpr hm
    convert! htransport using 1
    · funext v
      rw [Fin.prod_univ_succ]
      rfl
    · simp only [Fin.prod_univ_succ]

/-- The literal multi-index geometric series represents the original finite reciprocal. -/
theorem productSheetReciprocal_multi_hasSum (s : ℕ) {Z W : ℂ}
    (hZ : ‖Z‖ < 1) (hW : ‖W‖ ≤ 1) :
    HasSum (fun v : Fin s → ℕ =>
      ∏ i : Fin s, sheetZCoefficient (productSheetParameter s i) (v i) W * Z ^ (v i))
      (productSheetPolynomial s Z W)⁻¹ := by
  have h := hasSum_finiteSeriesProduct s
    (fun i k => sheetZCoefficient (productSheetParameter s i) k W * Z ^ k)
    (fun i => (sheetPolynomial (productSheetParameter s i) Z W)⁻¹)
    (fun i => sheetZCoefficient_hasSum (productSheetParameter_bounds s i).1.le
      (productSheetParameter_bounds s i).2 hW hZ)
  simpa only [Finset.prod_inv_distrib, productSheetPolynomial] using h

end

end MeyerGeneralProblem.StrongParity
